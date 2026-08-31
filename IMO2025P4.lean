module

public import Mathlib
public meta import Mathlib.Data.Nat.MaxPowDiv

public section Imo2025P4Section
namespace IMO2025P4
open Finset

private def top3 (n : ℕ) : List ℕ :=
  ((Nat.properDivisors n).sort (· ≤ ·)).reverse.take 3

private def next (n : ℕ) : ℕ := (top3 n).sum

private def Valid (n : ℕ) : Prop := 0 < n ∧ 3 ≤ #(Nat.properDivisors n)

private theorem exists_top3 {n : ℕ} (h : Valid n) :
    ∃ x y z, top3 n = [x, y, z] ∧ x ∈ Nat.properDivisors n ∧
      y ∈ Nat.properDivisors n ∧ z ∈ Nat.properDivisors n ∧
      x > y ∧ y > z ∧ ∀ d ∈ Nat.properDivisors n, d ≠ x → d ≠ y → d ≤ z := by
  let L := ((Nat.properDivisors n).sort (· ≤ ·)).reverse
  have hlen : 3 ≤ L.length := by simpa [L] using h.2
  have hshape : ∀ (L : List ℕ), 3 ≤ L.length → ∃ x y z t, L = x :: y :: z :: t := by
    intro l hl
    cases l with
    | nil => simp at hl
    | cons x l =>
      cases l with
      | nil => simp at hl
      | cons y l =>
        cases l with
        | nil => simp at hl
        | cons z t => exact ⟨x, y, z, t, rfl⟩
  obtain ⟨x, y, z, t, hL⟩ := hshape L hlen
  refine ⟨x, y, z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change L.take 3 = [x, y, z]
    simp [hL]
  · have : x ∈ L := by simp [hL]
    simpa [L] using this
  · have : y ∈ L := by simp [hL]
    simpa [L] using this
  · have : z ∈ L := by simp [hL]
    simpa [L] using this
  · have hs : L.SortedGT := by
      dsimp [L]
      exact List.sortedGT_reverse.mpr (Nat.properDivisors n).sortedLT_sort
    rw [hL] at hs
    exact hs.strictAnti_get
      (show (⟨0, by simp⟩ : Fin (x :: y :: z :: t).length) < ⟨1, by simp⟩ by
        exact Fin.mk_lt_mk.mpr (by omega))
  · have hs : L.SortedGT := by
      dsimp [L]
      exact List.sortedGT_reverse.mpr (Nat.properDivisors n).sortedLT_sort
    rw [hL] at hs
    exact hs.strictAnti_get
      (show (⟨1, by simp⟩ : Fin (x :: y :: z :: t).length) < ⟨2, by simp⟩ by
        exact Fin.mk_lt_mk.mpr (by omega))
  · intro d hd hdx hdy
    have hdL : d ∈ L := by simpa [L] using hd
    have hs : L.SortedGT := by
      dsimp [L]
      exact List.sortedGT_reverse.mpr (Nat.properDivisors n).sortedLT_sort
    rw [hL] at hdL hs
    simp only [List.mem_cons] at hdL
    rcases hdL with rfl | rfl | rfl | hdt
    · exact (hdx rfl).elim
    · exact (hdy rfl).elim
    · exact le_rfl
    · have hdpos : t.idxOf d < t.length := List.idxOf_lt_length_iff.mpr hdt
      have hbnd : 3 + t.idxOf d < (x :: y :: z :: t).length := by simp; omega
      have hrel := hs.strictAnti_get
        (show (⟨2, by simp⟩ : Fin (x :: y :: z :: t).length) <
            ⟨3 + t.idxOf d, hbnd⟩ by exact Fin.mk_lt_mk.mpr (by omega))
      have hrel' : t[t.idxOf d] < z := by
        simpa only [show 3 + t.idxOf d = (t.idxOf d).succ.succ.succ by omega,
          List.getElem_cons_succ, List.getElem_cons_zero] using hrel
      rw [List.getElem_idxOf hdpos] at hrel'
      exact hrel'.le

private theorem top3_eq_of_candidates {n x y z : ℕ} (hv : Valid n)
    (hx : x ∈ Nat.properDivisors n) (hy : y ∈ Nat.properDivisors n)
    (hz : z ∈ Nat.properDivisors n) (hxy : y < x) (hyz : z < y)
    (hmax : ∀ d ∈ Nat.properDivisors n, d ≠ x → d ≠ y → d ≤ z) :
    top3 n = [x, y, z] := by
  obtain ⟨x', y', z', ht, hx', hy', hz', hxy', hyz', hmax'⟩ := exists_top3 hv
  rw [ht]
  have hxx : x = x' := by
    apply le_antisymm
    · by_cases h : x = x'
      · exact h.le
      by_cases h2 : x = y'
      · subst x; omega
      · exact (hmax' x hx h h2).trans (by omega)
    · by_cases h : x' = x
      · exact h.le
      by_cases h2 : x' = y
      · subst x'; omega
      · exact (hmax x' hx' h h2).trans (by omega)
  subst x'
  have hyy : y = y' := by
    apply le_antisymm
    · by_cases h : y = x
      · subst y; omega
      by_cases h2 : y = y'
      · exact h2.le
      · exact (hmax' y hy h h2).trans (by omega)
    · by_cases h : y' = x
      · subst y'; omega
      by_cases h2 : y' = y
      · exact h2.le
      · exact (hmax y' hy' h h2).trans (by omega)
  subst y'
  have hzz : z = z' := by
    exact le_antisymm (hmax' z hz (by omega) (by omega))
      (hmax z' hz' (by omega) (by omega))
  subst z'
  rfl

private theorem mem_properDivisors_of_factor {d c n : ℕ} (hn : n ≠ 0) (hc : 1 < c)
    (h : n = d * c) : d ∈ Nat.properDivisors n := by
  apply (Nat.mem_properDivisors_iff_exists hn).2
  exact ⟨c, hc, h⟩

private theorem valid_twelve_mul (n : ℕ) (hn : 0 < n) : Valid (12 * n) := by
  refine ⟨by positivity, ?_⟩
  have hn0 : 12 * n ≠ 0 := by positivity
  have h6 : 6 * n ∈ Nat.properDivisors (12 * n) := by
    apply mem_properDivisors_of_factor hn0 (c := 2)
    · norm_num
    · omega
  have h4 : 4 * n ∈ Nat.properDivisors (12 * n) := by
    apply mem_properDivisors_of_factor hn0 (c := 3)
    · norm_num
    · omega
  have h3 : 3 * n ∈ Nat.properDivisors (12 * n) := by
    apply mem_properDivisors_of_factor hn0 (c := 4)
    · norm_num
    · omega
  have hs : {6 * n, 4 * n, 3 * n} ⊆ Nat.properDivisors (12 * n) := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    exacts [h6, h4, h3]
  have hc := Finset.card_le_card hs
  have hne64 : 6 * n ≠ 4 * n := by omega
  have hne63 : 6 * n ≠ 3 * n := by omega
  have hne43 : 4 * n ≠ 3 * n := by omega
  norm_num [hne64, hne63, hne43] at hc ⊢
  exact hc

private theorem next_twelve_mul (n : ℕ) (hn : 0 < n) : next (12 * n) = 13 * n := by
  have hn0 : 12 * n ≠ 0 := by positivity
  have hv := valid_twelve_mul n hn
  have h6 : 6 * n ∈ Nat.properDivisors (12 * n) := by
    apply mem_properDivisors_of_factor hn0 (c := 2)
    · norm_num
    · omega
  have h4 : 4 * n ∈ Nat.properDivisors (12 * n) := by
    apply mem_properDivisors_of_factor hn0 (c := 3)
    · norm_num
    · omega
  have h3 : 3 * n ∈ Nat.properDivisors (12 * n) := by
    apply mem_properDivisors_of_factor hn0 (c := 4)
    · norm_num
    · omega
  have ht : top3 (12 * n) = [6 * n, 4 * n, 3 * n] := by
    apply top3_eq_of_candidates hv h6 h4 h3 <;> try omega
    intro d hd hd6 hd4
    rw [Nat.mem_properDivisors_iff_exists hn0] at hd
    obtain ⟨c, hc, heq⟩ := hd
    by_contra hh
    have hdgt : 3 * n < d := by omega
    have hc_lt : c < 4 := by nlinarith
    interval_cases c <;> norm_num at hc
    · omega
    · omega
  rw [next, ht]
  simp
  ring

private theorem valid_six_mul_odd (m : ℕ) (hm : Odd m) : Valid (6 * m) := by
  have hm0 : 0 < m := Odd.pos hm
  refine ⟨by positivity, ?_⟩
  have hn0 : 6 * m ≠ 0 := by positivity
  have h3 : 3 * m ∈ Nat.properDivisors (6 * m) := by
    apply mem_properDivisors_of_factor hn0 (c := 2)
    · norm_num
    · omega
  have h2 : 2 * m ∈ Nat.properDivisors (6 * m) := by
    apply mem_properDivisors_of_factor hn0 (c := 3)
    · norm_num
    · omega
  have h1 : m ∈ Nat.properDivisors (6 * m) := by
    apply mem_properDivisors_of_factor hn0 (c := 6)
    · norm_num
    · omega
  have hs : {3 * m, 2 * m, m} ⊆ Nat.properDivisors (6 * m) := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    exacts [h3, h2, h1]
  have hc := Finset.card_le_card hs
  have hne32 : 3 * m ≠ 2 * m := by omega
  have hne31 : 3 * m ≠ m := by omega
  have hne21 : 2 * m ≠ m := by omega
  norm_num [hne32, hne31, hne21] at hc ⊢
  exact hc

private theorem next_six_mul_odd (m : ℕ) (hm : Odd m) (hm5 : ¬ 5 ∣ m) :
    next (6 * m) = 6 * m := by
  have hm0 : 0 < m := Odd.pos hm
  have hn0 : 6 * m ≠ 0 := by positivity
  have hv := valid_six_mul_odd m hm
  have h3 : 3 * m ∈ Nat.properDivisors (6 * m) := by
    apply mem_properDivisors_of_factor hn0 (c := 2)
    · norm_num
    · omega
  have h2 : 2 * m ∈ Nat.properDivisors (6 * m) := by
    apply mem_properDivisors_of_factor hn0 (c := 3)
    · norm_num
    · omega
  have h1 : m ∈ Nat.properDivisors (6 * m) := by
    apply mem_properDivisors_of_factor hn0 (c := 6)
    · norm_num
    · omega
  have ht : top3 (6 * m) = [3 * m, 2 * m, m] := by
    apply top3_eq_of_candidates hv h3 h2 h1 <;> try omega
    intro d hd hd3 hd2
    rw [Nat.mem_properDivisors_iff_exists hn0] at hd
    obtain ⟨c, hc, heq⟩ := hd
    by_contra hh
    have hdgt : m < d := by omega
    have hc_lt : c < 6 := by nlinarith
    interval_cases c
    all_goals norm_num at hc
    case hmax.«2» =>
      have hdeq : d = 3 * m := by omega
      exact hd3 hdeq
    case hmax.«3» =>
      have hdeq : d = 2 * m := by omega
      exact hd2 hdeq
    case hmax.«4» =>
      have h4 : 4 ∣ 6 * m := by rw [heq]; exact dvd_mul_left 4 d
      have hraw : 2 * 2 ∣ 2 * (3 * m) := by
        simpa only [show 2 * 2 = 4 by norm_num, show 2 * (3 * m) = 6 * m by ring] using h4
      have h2div3m : 2 ∣ 3 * m := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hraw
      have h2m := (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 2 3)).mp h2div3m
      exact hm.not_two_dvd_nat h2m
    case hmax.«5» =>
      have h5 : 5 ∣ 6 * m := by rw [heq]; exact dvd_mul_left 5 d
      have h5m := (Nat.Coprime.dvd_mul_right (by norm_num : Nat.Coprime 5 6)).mp
        (by simpa [mul_comm] using h5)
      exact hm5 h5m
  rw [next, ht]
  simp
  ring

private theorem proper_divisor_mul_two_le {d n : ℕ} (hd : d ∈ Nat.properDivisors n) :
    2 * d ≤ n := by
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    simp at hd
  rw [Nat.mem_properDivisors_iff_exists hn0] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  have h2c : 2 ≤ c := by omega
  nlinarith

private theorem six_dvd_of_le_next {n : ℕ} (hv : Valid n) (hle : n ≤ next n) : 6 ∣ n := by
  obtain ⟨x, y, z, ht, hx, hy, hz, hxy, hyz, hmax⟩ := exists_top3 hv
  have hnext : next n = x + y + z := by simp [next, ht, add_assoc]
  have hn0 : n ≠ 0 := by exact Nat.ne_of_gt hv.1
  have h2x := proper_divisor_mul_two_le hx
  by_contra h6
  have hnot2or3 : ¬ 2 ∣ n ∨ ¬ 3 ∣ n := by
    by_contra h
    push Not at h
    exact h6 ((Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3)) h.1 h.2)
  rcases hnot2or3 with hn2 | hn3
  · have bound (d : ℕ) (hd : d ∈ Nat.properDivisors n) : 3 * d ≤ n := by
      rw [Nat.mem_properDivisors_iff_exists hn0] at hd
      obtain ⟨c, hc, heq⟩ := hd
      have hc3 : 3 ≤ c := by
        by_contra h
        have hc2 : c = 2 := by omega
        subst c
        apply hn2
        use d
        omega
      nlinarith
    have hbx := bound x hx
    have hby := bound y hy
    have hbz := bound z hz
    rw [hnext] at hle
    omega
  · have boundy : 4 * y ≤ n := by
      rw [Nat.mem_properDivisors_iff_exists hn0] at hy
      obtain ⟨c, hc, heq⟩ := hy
      have hc4 : 4 ≤ c := by
        by_contra h
        have hc23 : c = 2 ∨ c = 3 := by omega
        rcases hc23 with rfl | rfl
        · have hxeq : x = y := by
            have h2xle : 2 * x ≤ n := proper_divisor_mul_two_le hx
            apply le_antisymm
            · nlinarith
            · omega
          omega
        · apply hn3
          use y
          omega
      nlinarith
    have boundz : 4 * z ≤ n := by
      rw [Nat.mem_properDivisors_iff_exists hn0] at hz
      obtain ⟨c, hc, heq⟩ := hz
      have hc4 : 4 ≤ c := by
        by_contra h
        have hc23 : c = 2 ∨ c = 3 := by omega
        rcases hc23 with rfl | rfl
        · have h2xle : 2 * x ≤ n := proper_divisor_mul_two_le hx
          nlinarith
        · apply hn3
          use z
          omega
      nlinarith
    have h2xn : 2 * x ≤ n := proper_divisor_mul_two_le hx
    rw [hnext] at hle
    omega

private theorem six_mul_le_next (t : ℕ) (hv : Valid (6 * t)) : 6 * t ≤ next (6 * t) := by
  have ht0 : 0 < t := by
    by_contra h
    have : t = 0 := by omega
    subst t
    simp [Valid] at hv
  have hn0 : 6 * t ≠ 0 := by positivity
  have h3 : 3 * t ∈ Nat.properDivisors (6 * t) := by
    apply mem_properDivisors_of_factor hn0 (c := 2)
    · norm_num
    · omega
  obtain ⟨x, y, z, htop, hx, hy, hz, hxy, hyz, hmax⟩ := exists_top3 hv
  have h3le : 3 * t ≤ x := by
    by_cases heq : 3 * t = x
    · omega
    by_cases heqy : 3 * t = y
    · omega
    exact (hmax (3 * t) h3 heq heqy).trans (by omega)
  have h2 : 2 * t ∈ Nat.properDivisors (6 * t) := by
    apply mem_properDivisors_of_factor hn0 (c := 3)
    · norm_num
    · omega
  have h2le : 2 * t ≤ y := by
    by_cases heq : 2 * t = x
    · omega
    by_cases heqy : 2 * t = y
    · omega
    exact (hmax (2 * t) h2 heq heqy).trans (by omega)
  have h1 : t ∈ Nat.properDivisors (6 * t) := by
    apply mem_properDivisors_of_factor hn0 (c := 6)
    · norm_num
    · omega
  have h1le : t ≤ z := by
    by_cases heq : t = x
    · omega
    by_cases heqy : t = y
    · omega
    exact hmax t h1 heq heqy
  simp [next, htop]
  omega

private theorem no_entry {n : ℕ} (hv : Valid n) (h6next : 6 ∣ next n) : 6 ∣ n := by
  obtain ⟨x, y, z, ht, hx, hy, hz, hxy, hyz, hmax⟩ := exists_top3 hv
  have hsum : next n = x + y + z := by simp [next, ht, add_assoc]
  rw [hsum] at h6next
  have h2sum : 2 ∣ x + y + z := dvd_trans (by norm_num) h6next
  have h3sum : 3 ∣ x + y + z := dvd_trans (by norm_num) h6next
  have hn0 : n ≠ 0 := Nat.ne_of_gt hv.1
  by_cases h2n : 2 ∣ n
  · by_cases h3n : 3 ∣ n
    · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2n h3n
    · exfalso
      have hn3 (d : ℕ) (hd : d ∈ Nat.properDivisors n) : ¬ 3 ∣ d :=
        fun h => h3n (dvd_trans h (Nat.mem_properDivisors.mp hd).1)
      have hx3 := hn3 x hx
      have hy3 := hn3 y hy
      have hz3 := hn3 z hz
      have heqmod : (x + y + z) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h3sum
      have hmods : x % 3 = y % 3 ∧ y % 3 = z % 3 := by
        have hxmod : x % 3 = 1 ∨ x % 3 = 2 := by omega
        have hymod : y % 3 = 1 ∨ y % 3 = 2 := by omega
        have hzmod : z % 3 = 1 ∨ z % 3 = 2 := by omega
        rcases hxmod with hxmod | hxmod <;>
          rcases hymod with hymod | hymod <;>
            rcases hzmod with hzmod | hzmod <;> omega
      have hxhalf : x = n / 2 := by
        apply le_antisymm
        · exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by
            simpa [mul_comm] using proper_divisor_mul_two_le hx)
        · have hd : n / 2 ∣ n := Nat.div_dvd_of_dvd h2n
          have hdmem : n / 2 ∈ Nat.properDivisors n :=
            Nat.mem_properDivisors.mpr ⟨hd, Nat.div_lt_self hv.1 (by norm_num)⟩
          by_cases he : n / 2 = x
          · omega
          by_cases he2 : n / 2 = y
          · omega
          exact (hmax (n / 2) hdmem he he2).trans (by omega)
      by_cases h4n : 4 ∣ n
      · have hyquarter : y = n / 4 := by
          apply le_antisymm
          · have hy4 : 4 * y ≤ n := by
              rw [Nat.mem_properDivisors_iff_exists hn0] at hy
              obtain ⟨c, hc, heq⟩ := hy
              have hc4 : 4 ≤ c := by
                by_contra h
                have hc23 : c = 2 ∨ c = 3 := by omega
                rcases hc23 with rfl | rfl
                · have h2y : 2 * y = n := by omega
                  have h2x : 2 * x ≤ n := proper_divisor_mul_two_le hx
                  omega
                · exact h3n ⟨y, by omega⟩
              nlinarith
            exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by simpa [mul_comm] using hy4)
          · have hd : n / 4 ∣ n := Nat.div_dvd_of_dvd h4n
            have hdmem : n / 4 ∈ Nat.properDivisors n :=
              Nat.mem_properDivisors.mpr ⟨hd, Nat.div_lt_self hv.1 (by norm_num)⟩
            by_cases he : n / 4 = x
            · have h2x : 2 * x ≤ n := proper_divisor_mul_two_le hx
              omega
            by_cases he2 : n / 4 = y
            · omega
            exact (hmax (n / 4) hdmem he he2).trans (by omega)
        have hdiv2 : n / 2 = 2 * (n / 4) := by omega
        have hx2y : x = 2 * y := by omega
        omega
      · have hxodd : Odd x := by
          rw [hxhalf]
          exact Nat.not_even_iff_odd.mp (by
            intro he
            apply h4n
            obtain ⟨s, hs⟩ := he
            obtain ⟨r, hr⟩ := h2n
            use s
            omega)
        have hxpar : x % 2 = 1 := Nat.odd_iff.mp hxodd
        have hsumEven : (x + y + z) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2sum
        have hyzOpp : y % 2 ≠ z % 2 := by omega
        have hyeven : 2 ∣ y := by
          by_contra hy2
          have hyodd : Odd y := Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hy2)
          have hyn2 : n / 2 ∣ n := Nat.div_dvd_of_dvd h2n
          have hydiv : y ∣ n := (Nat.mem_properDivisors.mp hy).1
          have h2ydiv : 2 * y ∣ n := by
            apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
            · exact hyodd.coprime_two_left
            · exact h2n
            · exact hydiv
          have h2ylt : 2 * y < n := by
            have hle := proper_divisor_mul_two_le hy
            apply lt_of_le_of_ne hle
            intro heq
            have hyhalf : y = n / 2 := by rw [← heq]; simp
            omega
          have h2ymem : 2 * y ∈ Nat.properDivisors n :=
            Nat.mem_properDivisors.mpr ⟨h2ydiv, h2ylt⟩
          by_cases he : 2 * y = x
          · have : 2 ∣ x := by exact ⟨y, he.symm⟩
            exact False.elim (hxodd.not_two_dvd_nat this)
          by_cases he2 : 2 * y = y
          · omega
          have := hmax (2 * y) h2ymem he he2
          omega
        have hzodd : Odd z := by
          have hzeven : ¬ 2 ∣ z := by
            intro hz2
            have : y % 2 = z % 2 := by
              rw [Nat.dvd_iff_mod_eq_zero] at hyeven hz2
              omega
            exact hyzOpp this
          exact Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hzeven)
        have h2zdiv : 2 * z ∣ n := by
          apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
          · exact hzodd.coprime_two_left
          · exact h2n
          · exact (Nat.mem_properDivisors.mp hz).1
        have h2zlt : 2 * z < n := by
          have hle := proper_divisor_mul_two_le hz
          apply lt_of_le_of_ne hle
          intro heq
          have hzhalf : z = n / 2 := by rw [← heq]; simp
          omega
        have h2zmem : 2 * z ∈ Nat.properDivisors n :=
          Nat.mem_properDivisors.mpr ⟨h2zdiv, h2zlt⟩
        have hy2z : y = 2 * z := by
          by_cases he : 2 * z = x
          · have : 2 ∣ x := by exact ⟨z, he.symm⟩
            exact False.elim (hxodd.not_two_dvd_nat this)
          by_cases he2 : 2 * z = y
          · omega
          have hzbound := hmax (2 * z) h2zmem he he2
          have hzpos := Nat.pos_of_mem_properDivisors hz
          omega
        omega
  · exfalso
    have hnodd : Odd n := Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using h2n)
    have oddd (d : ℕ) (hd : d ∈ Nat.properDivisors n) : Odd d :=
      hnodd.of_dvd_nat (Nat.mem_properDivisors.mp hd).1
    obtain ⟨rx, hrx⟩ := oddd x hx
    obtain ⟨ry, hry⟩ := oddd y hy
    obtain ⟨rz, hrz⟩ := oddd z hz
    obtain ⟨q, hq⟩ := h2sum
    omega

private theorem le_next_iff_six_dvd {n : ℕ} (hv : Valid n) : n ≤ next n ↔ 6 ∣ n := by
  refine ⟨six_dvd_of_le_next hv, ?_⟩
  rintro ⟨t, rfl⟩
  exact six_mul_le_next t hv

private theorem infinite_recurrence_six_dvd (a : ℕ → ℕ)
    (hv : ∀ i, Valid (a i)) (hrec : ∀ i, a (i + 1) = next (a i)) : ∀ i, 6 ∣ a i := by
  intro i
  by_contra h6
  have descent {n : ℕ} (hnv : Valid n) (hn6 : ¬ 6 ∣ n) : next n < n := by
    have := (le_next_iff_six_dvd hnv).not.mpr hn6
    omega
  have preserve {n : ℕ} (hnv : Valid n) (hn6 : ¬ 6 ∣ n) : ¬ 6 ∣ next n := by
    intro h
    exact hn6 (no_entry hnv h)
  have aux : ∀ N i, a i = N → ¬ 6 ∣ a i → False := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro j hj hj6
      have hlt : a (j + 1) < N := by
        rw [← hj, hrec]
        exact descent (hv j) hj6
      apply ih (a (j + 1)) hlt (j + 1) rfl
      rw [hrec]
      exact preserve (hv j) hj6
  exact aux (a i) i rfl h6

private theorem next_six_mul_even (m : ℕ) (hm : 0 < m) (he : 2 ∣ m) :
    next (6 * m) = 13 * (m / 2) := by
  obtain ⟨r, hr⟩ := he
  subst m
  have hr0 : 0 < r := by omega
  rw [show 6 * (2 * r) = 12 * r by ring, next_twelve_mul r hr0]
  simp [mul_comm]

private theorem next_thirty_mul (r : ℕ) (hr : Odd r) : next (30 * r) = 31 * r := by
  have hr0 : 0 < r := Odd.pos hr
  have hn0 : 30 * r ≠ 0 := by positivity
  have h15 : 15 * r ∈ Nat.properDivisors (30 * r) := by
    apply mem_properDivisors_of_factor hn0 (c := 2)
    · norm_num
    · omega
  have h10 : 10 * r ∈ Nat.properDivisors (30 * r) := by
    apply mem_properDivisors_of_factor hn0 (c := 3)
    · norm_num
    · omega
  have h6 : 6 * r ∈ Nat.properDivisors (30 * r) := by
    apply mem_properDivisors_of_factor hn0 (c := 5)
    · norm_num
    · omega
  have hv : Valid (30 * r) := by
    refine ⟨by positivity, ?_⟩
    have hs : {15 * r, 10 * r, 6 * r} ⊆ Nat.properDivisors (30 * r) := by
      intro d hd
      simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl | rfl
      exacts [h15, h10, h6]
    have hc := Finset.card_le_card hs
    have h1 : 15 * r ≠ 10 * r := by omega
    have h2 : 15 * r ≠ 6 * r := by omega
    have h3 : 10 * r ≠ 6 * r := by omega
    norm_num [h1, h2, h3] at hc ⊢
    exact hc
  have ht : top3 (30 * r) = [15 * r, 10 * r, 6 * r] := by
    apply top3_eq_of_candidates hv h15 h10 h6 <;> try omega
    intro d hd hd15 hd10
    rw [Nat.mem_properDivisors_iff_exists hn0] at hd
    obtain ⟨c, hc, heq⟩ := hd
    by_contra hh
    have hdgt : 6 * r < d := by omega
    have hc_lt : c < 5 := by nlinarith
    interval_cases c
    all_goals norm_num at hc
    case hmax.«2» => exact hd15 (by omega)
    case hmax.«3» => exact hd10 (by omega)
    case hmax.«4» =>
      have h4r : 4 ∣ 30 * r := by rw [heq]; exact dvd_mul_left 4 d
      have hraw : 2 * 2 ∣ 2 * (15 * r) := by
        simpa only [show 2 * 2 = 4 by norm_num, show 2 * (15 * r) = 30 * r by ring] using h4r
      have h2div : 2 ∣ 15 * r := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hraw
      have h2r := (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 2 15)).mp h2div
      exact hr.not_two_dvd_nat h2r
  rw [next, ht]
  simp
  ring

private theorem core_of_next_six_dvd {m : ℕ} (hm : 0 < m) (h12 : ¬ 12 ∣ m)
    (h6 : 6 ∣ next (6 * m)) : Odd m ∧ ¬ 5 ∣ m := by
  by_cases h2m : 2 ∣ m
  · rw [next_six_mul_even m hm h2m] at h6
    have h6half : 6 ∣ m / 2 :=
      (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 6 13)).mp h6
    apply False.elim
    apply h12
    obtain ⟨r, hr⟩ := h6half
    use r
    omega
  · have hodd : Odd m := Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using h2m)
    refine ⟨hodd, ?_⟩
    intro h5
    obtain ⟨r, hr⟩ := h5
    subst m
    have hrOdd : Odd r := hodd.of_dvd_nat ⟨5, by ring⟩
    rw [show 6 * (5 * r) = 30 * r by ring, next_thirty_mul r hrOdd] at h6
    have h6r : 6 ∣ r :=
      (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 6 31)).mp h6
    apply h12
    obtain ⟨s, hs⟩ := h6r
    use s * 5
    omega

private theorem recurrence_strip_twelve (a : ℕ → ℕ) (hrec : ∀ i, a (i + 1) = next (a i))
    (k m : ℕ) (hm : 0 < m) (h0 : a 0 = 6 * 12 ^ k * m) :
    a k = 6 * 13 ^ k * m := by
  induction k generalizing a m with
  | zero => simpa using h0
  | succ k ih =>
    let b : ℕ → ℕ := fun i => a (i + 1)
    have hbrec : ∀ i, b (i + 1) = next (b i) := by
      intro i
      dsimp [b]
      rw [show i + 1 + 1 = (i + 1) + 1 by omega, hrec]
    have hfactor : a 0 = 12 * (6 * 12 ^ k * m) := by
      rw [h0, pow_succ]
      ring
    have hinner : 0 < 6 * 12 ^ k * m := by positivity
    have hb0 : b 0 = 6 * 12 ^ k * (13 * m) := by
      dsimp [b]
      rw [hrec, hfactor, next_twelve_mul (6 * 12 ^ k * m) hinner]
      ring
    have hbm : 0 < 13 * m := by positivity
    have hih := @ih b hbrec (13 * m) hbm hb0
    dsimp [b] at hih
    rw [show k + 1 = k.succ by omega]
    rw [hih, pow_succ]
    ring

private theorem classify_initial (a : ℕ → ℕ) (hv : ∀ i, Valid (a i))
    (hrec : ∀ i, a (i + 1) = next (a i)) :
    ∃ k m, a 0 = 6 * 12 ^ k * m ∧ Odd m ∧ ¬ 5 ∣ m := by
  have h6all := infinite_recurrence_six_dvd a hv hrec
  obtain ⟨q, hq⟩ := h6all 0
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    have hpos := (hv 0).1
    simp at hq
    omega
  let k := padicValNat 12 q
  let m := Nat.divMaxPow q 12
  have hdecomp : 12 ^ k * m = q := by
    simp [k, m]
  have hm0 : 0 < m := by
    by_contra h
    have hmz : m = 0 := by omega
    rw [hmz] at hdecomp
    simp at hdecomp
    exact hq0 hdecomp.symm
  have hm12 : ¬ 12 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq0
  have ha0 : a 0 = 6 * 12 ^ k * m := by
    calc
      a 0 = 6 * q := hq
      _ = 6 * (12 ^ k * m) := by rw [hdecomp]
      _ = 6 * 12 ^ k * m := by ring
  have hak : a k = 6 * 13 ^ k * m :=
    recurrence_strip_twelve a hrec k m hm0 ha0
  have hu0 : 0 < 13 ^ k * m := by positivity
  have hu12 : ¬ 12 ∣ 13 ^ k * m := by
    intro h
    have hcop : Nat.Coprime 12 (13 ^ k) := by
      exact (by norm_num : Nat.Coprime 12 13).pow_right k
    exact hm12 (hcop.dvd_of_dvd_mul_left h)
  have hnext : 6 ∣ next (6 * (13 ^ k * m)) := by
    have heq : 6 * (13 ^ k * m) = a k := by rw [hak]; ring
    rw [heq, ← hrec k]
    exact h6all (k + 1)
  have hcore := core_of_next_six_dvd hu0 hu12 hnext
  have hmOdd : Odd m := hcore.1.of_dvd_nat (dvd_mul_left m (13 ^ k))
  have hm5 : ¬ 5 ∣ m := by
    intro h5
    exact hcore.2 (dvd_mul_of_dvd_right h5 (13 ^ k))
  exact ⟨k, m, ha0, hmOdd, hm5⟩

private theorem construct_sequence (k m : ℕ) (hm : Odd m) (hm5 : ¬ 5 ∣ m) :
    ∃ a : ℕ → ℕ,
      a 0 = 6 * 12 ^ k * m ∧ ∀ i, Valid (a i) ∧ a (i + 1) = next (a i) := by
  let a : ℕ → ℕ := fun i =>
    if i ≤ k then 6 * 12 ^ (k - i) * 13 ^ i * m else 6 * 13 ^ k * m
  have hodd13 (j : ℕ) : Odd (13 ^ j * m) := by
    apply Odd.mul
    · apply Odd.pow
      norm_num
    · exact hm
  have hnot5 (j : ℕ) : ¬ 5 ∣ 13 ^ j * m := by
    intro h5
    exact hm5 ((Nat.Coprime.dvd_mul_left
      ((by norm_num : Nat.Coprime 5 13).pow_right j)).mp h5)
  refine ⟨a, ?_, ?_⟩
  · simp [a]
  · intro i
    constructor
    · by_cases hi : i ≤ k
      · change Valid (if i ≤ k then 6 * 12 ^ (k - i) * 13 ^ i * m else 6 * 13 ^ k * m)
        rw [if_pos hi]
        by_cases hik : i = k
        · subst i
          simp
          simpa [mul_assoc] using valid_six_mul_odd (13 ^ k * m) (hodd13 k)
        · have hlt : i < k := by omega
          have heq : 6 * 12 ^ (k - i) * 13 ^ i * m =
              12 * (6 * 12 ^ (k - (i + 1)) * 13 ^ i * m) := by
            rw [show k - i = (k - (i + 1)) + 1 by omega, pow_succ]
            ring
          rw [heq]
          apply valid_twelve_mul
          have hmpos : 0 < m := Odd.pos hm
          positivity
      · change Valid (if i ≤ k then 6 * 12 ^ (k - i) * 13 ^ i * m else 6 * 13 ^ k * m)
        rw [if_neg hi]
        simpa [mul_assoc] using valid_six_mul_odd (13 ^ k * m) (hodd13 k)
    · change (if i + 1 ≤ k then 6 * 12 ^ (k - (i + 1)) * 13 ^ (i + 1) * m else
          6 * 13 ^ k * m) =
        next (if i ≤ k then 6 * 12 ^ (k - i) * 13 ^ i * m else 6 * 13 ^ k * m)
      by_cases hlt : i < k
      · have hi : i ≤ k := by omega
        have hi1 : i + 1 ≤ k := by omega
        rw [if_pos hi, if_pos hi1]
        have heq : 6 * 12 ^ (k - i) * 13 ^ i * m =
            12 * (6 * 12 ^ (k - (i + 1)) * 13 ^ i * m) := by
          rw [show k - i = (k - (i + 1)) + 1 by omega, pow_succ]
          ring
        rw [heq, next_twelve_mul]
        · rw [pow_succ]
          ring
        · have hmpos : 0 < m := Odd.pos hm
          positivity
      · have hi1 : ¬ i + 1 ≤ k := by omega
        rw [if_neg hi1]
        by_cases hi : i ≤ k
        · have hik : i = k := by omega
          rw [if_pos hi]
          subst i
          simp
          have hfix := next_six_mul_odd (13 ^ k * m) (hodd13 k) (hnot5 k)
          simpa [mul_assoc] using hfix.symm
        · rw [if_neg hi]
          have hfix := next_six_mul_odd (13 ^ k * m) (hodd13 k) (hnot5 k)
          simpa [mul_assoc] using hfix.symm

/- determine -/ abbrev answer : Set ℕ :=
  {n | ∃ k m : ℕ, n = 6 * 12 ^ k * m ∧ Odd m ∧ ¬ 5 ∣ m}

theorem imo2025_p4 : {a₁ | ∃ a : ℕ → ℕ, a 0 = a₁ ∧ ∀ i, 0 < a i ∧ 3 ≤ #(Nat.properDivisors (a i)) ∧
    a (i + 1) = (((Nat.properDivisors (a i)).sort (· ≤ ·)).reverse.take 3).sum} = answer := by
  ext a₁
  constructor
  · rintro ⟨a, ha0, ha⟩
    have hv : ∀ i, Valid (a i) := fun i => ⟨(ha i).1, (ha i).2.1⟩
    have hrec : ∀ i, a (i + 1) = next (a i) := by
      intro i
      exact (ha i).2.2
    obtain ⟨k, m, h0, hm, hm5⟩ := classify_initial a hv hrec
    exact ⟨k, m, ha0.symm.trans h0, hm, hm5⟩
  · rintro ⟨k, m, h0, hm, hm5⟩
    obtain ⟨a, ha0, ha⟩ := construct_sequence k m hm hm5
    refine ⟨a, ?_, ?_⟩
    · exact ha0.trans h0.symm
    · intro i
      exact ⟨(ha i).1.1, (ha i).1.2, (ha i).2⟩
end IMO2025P4
