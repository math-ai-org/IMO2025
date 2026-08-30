import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace IMO2025P4

open Finset

set_option autoImplicit false

abbrev answer : Set ℕ := {n | ∃ k m : ℕ, n = 6 * 12^k * m ∧ Odd m ∧ ¬ 5 ∣ m}

private def step (n : ℕ) : ℕ :=
  (((Nat.properDivisors n).sort (· ≤ ·)).reverse.take 3).sum

private def Admissible (n : ℕ) : Prop :=
  0 < n ∧ 3 ≤ #(Nat.properDivisors n)

private lemma reverse_sort_eq_sort_ge (s : Finset ℕ) :
    (s.sort (· ≤ ·)).reverse = s.sort (· ≥ ·) := by
  exact (s.sortedGT_sort.eq_reverse_of_mem_iff_of_sortedLT (by simp) s.sortedLT_sort).symm

private lemma step_eq_of_three_largest {n x y z : ℕ}
    (hx : x ∈ Nat.properDivisors n)
    (hy : y ∈ Nat.properDivisors n) (hyx : y ≠ x)
    (hz : z ∈ Nat.properDivisors n) (hzx : z ≠ x) (hzy : z ≠ y)
    (h₁ : ∀ d ∈ Nat.properDivisors n, d ≤ x)
    (h₂ : ∀ d ∈ Nat.properDivisors n, d ≠ x → d ≤ y)
    (h₃ : ∀ d ∈ Nat.properDivisors n, d ≠ x → d ≠ y → d ≤ z) :
    step n = x + y + z := by
  let s := Nat.properDivisors n
  have hx' : x ∈ s := by exact hx
  have hsort₁ : s.sort (· ≥ ·) = x :: (s.erase x).sort (· ≥ ·) := by
    calc
      s.sort (· ≥ ·) = (insert x (s.erase x)).sort (· ≥ ·) := by
        rw [Finset.insert_erase hx']
      _ = x :: (s.erase x).sort (· ≥ ·) := by
        apply Finset.sort_insert (fun a b : ℕ => a ≥ b)
        · intro d hd
          exact h₁ d (Finset.mem_of_mem_erase hd)
        · exact Finset.notMem_erase x s
  have hy' : y ∈ s.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
  have hsort₂ : (s.erase x).sort (· ≥ ·) =
      y :: ((s.erase x).erase y).sort (· ≥ ·) := by
    calc
      (s.erase x).sort (· ≥ ·) =
          (insert y ((s.erase x).erase y)).sort (· ≥ ·) := by
        rw [Finset.insert_erase hy']
      _ = y :: ((s.erase x).erase y).sort (· ≥ ·) := by
        apply Finset.sort_insert (fun a b : ℕ => a ≥ b)
        · intro d hd
          have hd' := Finset.mem_of_mem_erase hd
          exact h₂ d (Finset.mem_of_mem_erase hd') (Finset.mem_erase.mp hd').1
        · exact Finset.notMem_erase y (s.erase x)
  have hz' : z ∈ (s.erase x).erase y := by
    exact Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzx, hz⟩⟩
  have hsort₃ : ((s.erase x).erase y).sort (· ≥ ·) =
      z :: (((s.erase x).erase y).erase z).sort (· ≥ ·) := by
    calc
      ((s.erase x).erase y).sort (· ≥ ·) =
          (insert z (((s.erase x).erase y).erase z)).sort (· ≥ ·) := by
        rw [Finset.insert_erase hz']
      _ = z :: (((s.erase x).erase y).erase z).sort (· ≥ ·) := by
        apply Finset.sort_insert (fun a b : ℕ => a ≥ b)
        · intro d hd
          have hd' := Finset.mem_of_mem_erase hd
          have hd'' := Finset.mem_of_mem_erase hd'
          exact h₃ d (Finset.mem_of_mem_erase hd'')
            (Finset.mem_erase.mp hd'').1 (Finset.mem_erase.mp hd').1
        · exact Finset.notMem_erase z ((s.erase x).erase y)
  rw [step, reverse_sort_eq_sort_ge, hsort₁, hsort₂, hsort₃]
  simp only [List.take, List.sum_cons, List.sum_nil]
  omega

private lemma exists_three_largest {n : ℕ} (hcard : 3 ≤ #(Nat.properDivisors n)) :
    ∃ x y z : ℕ,
      x ∈ Nat.properDivisors n ∧ y ∈ Nat.properDivisors n ∧ z ∈ Nat.properDivisors n ∧
      y < x ∧ z < y ∧
      (∀ d ∈ Nat.properDivisors n, d ≤ x) ∧
      (∀ d ∈ Nat.properDivisors n, d ≠ x → d ≤ y) ∧
      (∀ d ∈ Nat.properDivisors n, d ≠ x → d ≠ y → d ≤ z) := by
  let s := Nat.properDivisors n
  let l := s.sort (· ≥ ·)
  have hlen : 3 ≤ l.length := by simpa [l, s] using hcard
  have hmem : ∀ d, d ∈ l ↔ d ∈ s := by
    intro d
    simp [l]
  have hpair : l.Pairwise (· > ·) := by
    exact (s.sortedGT_sort).pairwise
  cases hl : l with
  | nil => simp [hl] at hlen
  | cons x l₁ =>
      cases hl₁ : l₁ with
      | nil => simp [hl, hl₁] at hlen
      | cons y l₂ =>
          cases hl₂ : l₂ with
          | nil => simp [hl, hl₁, hl₂] at hlen
          | cons z r =>
              have hlxyz : l = x :: y :: z :: r := by simp [hl, hl₁, hl₂]
              have hp : (x :: y :: z :: r).Pairwise (· > ·) := hlxyz ▸ hpair
              simp only [List.pairwise_cons] at hp
              rcases hp with ⟨hpx, hpy, hpz, _⟩
              have hx : x ∈ Nat.properDivisors n := by
                change x ∈ s
                exact (hmem x).mp (by simp [hlxyz])
              have hy : y ∈ Nat.properDivisors n := by
                change y ∈ s
                exact (hmem y).mp (by simp [hlxyz])
              have hz : z ∈ Nat.properDivisors n := by
                change z ∈ s
                exact (hmem z).mp (by simp [hlxyz])
              refine ⟨x, y, z, hx, hy, hz, hpx y (by simp), hpy z (by simp), ?_, ?_, ?_⟩
              · intro d hd
                have hdl : d ∈ x :: y :: z :: r := by
                  rw [← hlxyz, hmem]
                  exact hd
                rcases List.mem_cons.mp hdl with rfl | hdt
                · exact Nat.le_refl _
                · exact Nat.le_of_lt (hpx d hdt)
              · intro d hd hdx
                have hdl : d ∈ x :: y :: z :: r := by
                  rw [← hlxyz, hmem]
                  exact hd
                rcases List.mem_cons.mp hdl with hdx' | hdt
                · exact (hdx hdx').elim
                · rcases List.mem_cons.mp hdt with rfl | hdrest
                  · exact Nat.le_refl _
                  · exact Nat.le_of_lt (hpy d hdrest)
              · intro d hd hdx hdy
                have hdl : d ∈ x :: y :: z :: r := by
                  rw [← hlxyz, hmem]
                  exact hd
                rcases List.mem_cons.mp hdl with hdx' | hdt
                · exact (hdx hdx').elim
                · rcases List.mem_cons.mp hdt with hdy' | hdrest
                  · exact (hdy hdy').elim
                  · rcases List.mem_cons.mp hdrest with rfl | hdr
                    · exact Nat.le_refl _
                    · exact Nat.le_of_lt (hpz d hdr)

private lemma step_spec {n : ℕ} (hcard : 3 ≤ #(Nat.properDivisors n)) :
    ∃ x y z : ℕ,
      step n = x + y + z ∧
      x ∈ Nat.properDivisors n ∧ y ∈ Nat.properDivisors n ∧ z ∈ Nat.properDivisors n ∧
      y < x ∧ z < y ∧
      (∀ d ∈ Nat.properDivisors n, d ≤ x) ∧
      (∀ d ∈ Nat.properDivisors n, d ≠ x → d ≤ y) ∧
      (∀ d ∈ Nat.properDivisors n, d ≠ x → d ≠ y → d ≤ z) := by
  obtain ⟨x, y, z, hx, hy, hz, hyx, hzy, h₁, h₂, h₃⟩ := exists_three_largest hcard
  exact ⟨x, y, z,
    step_eq_of_three_largest hx hy hyx.ne hz (ne_of_lt (hzy.trans hyx)) hzy.ne h₁ h₂ h₃,
    hx, hy, hz, hyx, hzy, h₁, h₂, h₃⟩

private lemma cofactor_lt_of_lt {n x y qx qy : ℕ} (hyx : y < x)
    (hx : n = x * qx) (hy : n = y * qy) (hqy : 0 < qy) : qx < qy := by
  by_contra h
  have hle : qy ≤ qx := Nat.le_of_not_gt h
  have hlt : y * qy < x * qx :=
    lt_of_lt_of_le ((Nat.mul_lt_mul_right hqy).mpr hyx) (Nat.mul_le_mul_left x hle)
  rw [← hy, ← hx] at hlt
  exact (Nat.lt_irrefl n) hlt

private lemma two_mul_dvd_of_odd_dvd {n d : ℕ} (hn : 2 ∣ n) (hd : d ∣ n) (hodd : Odd d) :
    2 * d ∣ n := by
  simpa [mul_comm] using hodd.coprime_two_left.mul_dvd_of_dvd_of_dvd hn hd

private lemma not_two_dvd_step {n : ℕ} (hcard : 3 ≤ #(Nat.properDivisors n))
    (hn2 : ¬2 ∣ n) : ¬2 ∣ step n := by
  obtain ⟨x, y, z, hstep, hx, hy, hz, hyx, hzy, h₁, h₂, h₃⟩ := step_spec hcard
  have hxodd : Odd x := by
    apply Nat.not_even_iff_odd.mp
    intro hxev
    exact hn2 ((even_iff_two_dvd.mp hxev).trans (Nat.mem_properDivisors.mp hx).1)
  have hyodd : Odd y := by
    apply Nat.not_even_iff_odd.mp
    intro hyev
    exact hn2 ((even_iff_two_dvd.mp hyev).trans (Nat.mem_properDivisors.mp hy).1)
  have hzodd : Odd z := by
    apply Nat.not_even_iff_odd.mp
    intro hzev
    exact hn2 ((even_iff_two_dvd.mp hzev).trans (Nat.mem_properDivisors.mp hz).1)
  intro htwo
  rcases hxodd with ⟨a, ha⟩
  rcases hyodd with ⟨b, hb⟩
  rcases hzodd with ⟨c, hc⟩
  rcases htwo with ⟨q, hq⟩
  rw [hstep] at hq
  omega

private lemma mod_three_ne_zero {a : ℕ} (ha : ¬3 ∣ a) : a % 3 = 1 ∨ a % 3 = 2 := by
  rw [Nat.dvd_iff_mod_eq_zero] at ha
  omega

private lemma mod_three_double_ne_self {a : ℕ} (ha : ¬3 ∣ a) : (2 * a) % 3 ≠ a % 3 := by
  rcases mod_three_ne_zero ha with h | h <;> omega

private lemma not_six_dvd_step {n : ℕ} (hnpos : 0 < n)
    (hcard : 3 ≤ #(Nat.properDivisors n)) (hn6 : ¬6 ∣ n) : ¬6 ∣ step n := by
  by_cases hn2 : 2 ∣ n
  · have hn3 : ¬3 ∣ n := by
      intro hn3
      exact hn6 ((by norm_num : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd hn2 hn3)
    obtain ⟨x, y, z, hstep, hx, hy, hz, hyx, hzy, h₁, h₂, h₃⟩ := step_spec hcard
    have hnx : n = 2 * x := by
      have hhalf : n / 2 ∈ Nat.properDivisors n := by
        apply Nat.mem_properDivisors.mpr
        constructor
        · exact Nat.div_dvd_of_dvd hn2
        · exact Nat.div_lt_self hnpos (by norm_num)
      have hle : n / 2 ≤ x := h₁ _ hhalf
      have hxle : x ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by
        obtain ⟨q, hq, hnq⟩ :=
          (Nat.mem_properDivisors_iff_exists (Nat.ne_of_gt hnpos)).mp hx
        calc
          x * 2 ≤ x * q := Nat.mul_le_mul_left x (by omega)
          _ = n := hnq.symm)
      have heq : x = n / 2 := Nat.le_antisymm hxle hle
      rw [heq, Nat.mul_div_cancel' hn2]
    have hx3 : ¬3 ∣ x := fun h => hn3 (h.trans (Nat.mem_properDivisors.mp hx).1)
    have hy3 : ¬3 ∣ y := fun h => hn3 (h.trans (Nat.mem_properDivisors.mp hy).1)
    have hz3 : ¬3 ∣ z := fun h => hn3 (h.trans (Nat.mem_properDivisors.mp hz).1)
    intro hstep6
    have hmods : x % 3 = y % 3 ∧ y % 3 = z % 3 := by
      rcases mod_three_ne_zero hx3 with hxmod | hxmod <;>
        rcases mod_three_ne_zero hy3 with hymod | hymod <;>
        rcases mod_three_ne_zero hz3 with hzmod | hzmod
      all_goals rcases hstep6 with ⟨q, hq⟩
      all_goals rw [hstep] at hq
      all_goals omega
    by_cases hn4 : 4 ∣ n
    · obtain ⟨t, ht⟩ := hn4
      have htmem : t ∈ Nat.properDivisors n := by
        apply Nat.mem_properDivisors.mpr
        constructor
        · refine ⟨4, ?_⟩
          rw [ht]
          omega
        · rw [ht]
          have htpos : 0 < t := by omega
          omega
      have htx : t ≠ x := by
        intro heq
        subst t
        rw [hnx] at ht
        omega
      have htle : t ≤ y := h₂ _ htmem htx
      obtain ⟨qy, hqy, hnqy⟩ :=
        (Nat.mem_properDivisors_iff_exists (Nat.ne_of_gt hnpos)).mp hy
      have hqy4 : 4 ≤ qy := by
        have hqy3 : 3 ≤ qy := by
          by_contra h
          have : qy = 2 := by omega
          rw [this, hnx] at hnqy
          omega
        by_contra h
        have : qy = 3 := by omega
        apply hn3
        rw [hnqy, this]
        exact dvd_mul_left 3 y
      have hylet : y ≤ t := by
        have : 4 * y ≤ n := calc
          4 * y ≤ qy * y := Nat.mul_le_mul_right y hqy4
          _ = y * qy := by ac_rfl
          _ = n := hnqy.symm
        rw [ht] at this
        omega
      have hyeq : y = t := Nat.le_antisymm hylet htle
      have hx2y : x = 2 * y := by omega
      exact (mod_three_double_ne_self hy3) (by simpa [hx2y] using hmods.1)
    · have hxodd : Odd x := by
        apply Nat.not_even_iff_odd.mp
        intro hxeven
        rcases hxeven with ⟨t, ht⟩
        apply hn4
        refine ⟨t, ?_⟩
        rw [hnx, ht]
        omega
      have hyeven : Even y := by
        rcases Nat.even_or_odd y with h | hyodd
        · exact h
        · exfalso
          have h2ydvd : 2 * y ∣ n := two_mul_dvd_of_odd_dvd hn2
            (Nat.mem_properDivisors.mp hy).1 hyodd
          have h2ylt : 2 * y < n := by
            by_contra h
            have hle : 2 * y ≤ n := Nat.le_of_dvd hnpos h2ydvd
            have heq : 2 * y = n := Nat.le_antisymm hle (Nat.le_of_not_gt h)
            rw [hnx] at heq
            omega
          have h2ymem : 2 * y ∈ Nat.properDivisors n :=
            Nat.mem_properDivisors.mpr ⟨h2ydvd, h2ylt⟩
          have h2yx : 2 * y ≠ x := by
            intro heq
            rcases hxodd with ⟨a, ha⟩
            omega
          have h2yle := h₂ _ h2ymem h2yx
          have hypos := Nat.pos_of_mem_properDivisors (n := n) hy
          omega
      have hzeven : Even z := by
        rcases Nat.even_or_odd z with h | hzodd
        · exact h
        · exfalso
          have h2zdvd : 2 * z ∣ n := two_mul_dvd_of_odd_dvd hn2
            (Nat.mem_properDivisors.mp hz).1 hzodd
          have h2zlt : 2 * z < n := by
            by_contra h
            have hle : 2 * z ≤ n := Nat.le_of_dvd hnpos h2zdvd
            have heq : 2 * z = n := Nat.le_antisymm hle (Nat.le_of_not_gt h)
            rw [hnx] at heq
            omega
          have h2zmem : 2 * z ∈ Nat.properDivisors n :=
            Nat.mem_properDivisors.mpr ⟨h2zdvd, h2zlt⟩
          have h2zx : 2 * z ≠ x := by
            intro heq
            rcases hxodd with ⟨a, ha⟩
            omega
          have h2zle : 2 * z ≤ y := h₂ _ h2zmem h2zx
          have h2zy : 2 * z = y := by
            by_contra hne
            have hzpos := Nat.pos_of_mem_properDivisors (n := n) hz
            have hbad := h₃ _ h2zmem h2zx hne
            omega
          exact (mod_three_double_ne_self hz3) (by simpa [h2zy] using hmods.2)
      rcases hxodd with ⟨a, ha⟩
      rcases hyeven with ⟨b, hb⟩
      rcases hzeven with ⟨c, hc⟩
      rcases hstep6 with ⟨q, hq⟩
      rw [hstep] at hq
      omega
  · intro hstep6
    exact not_two_dvd_step hcard hn2 (dvd_trans (by norm_num) hstep6)

private lemma step_lt_of_not_six_dvd {n : ℕ} (hnpos : 0 < n)
    (hcard : 3 ≤ #(Nat.properDivisors n)) (hn6 : ¬6 ∣ n) : step n < n := by
  obtain ⟨x, y, z, hstep, hx, hy, hz, hyx, hzy, h₁, h₂, h₃⟩ := step_spec hcard
  obtain ⟨qx, hqx, hnqx⟩ :=
    (Nat.mem_properDivisors_iff_exists (Nat.ne_of_gt hnpos)).mp hx
  obtain ⟨qy, hqy, hnqy⟩ :=
    (Nat.mem_properDivisors_iff_exists (Nat.ne_of_gt hnpos)).mp hy
  obtain ⟨qz, hqz, hnqz⟩ :=
    (Nat.mem_properDivisors_iff_exists (Nat.ne_of_gt hnpos)).mp hz
  have hqxy : qx < qy := cofactor_lt_of_lt hyx hnqx hnqy (by omega)
  have hqyz : qy < qz := cofactor_lt_of_lt hzy hnqy hnqz (by omega)
  have hn2or3 : ¬2 ∣ n ∨ ¬3 ∣ n := by
    by_contra h
    push Not at h
    exact hn6 ((by norm_num : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h.1 h.2)
  have hqy4 : 4 ≤ qy := by
    rcases hn2or3 with hn2 | hn3
    · have hqx3 : 3 ≤ qx := by
        by_contra h
        have : qx = 2 := by omega
        apply hn2
        rw [hnqx, this]
        exact dvd_mul_left 2 x
      omega
    · have hqy3 : 3 ≤ qy := by omega
      by_contra h
      have : qy = 3 := by omega
      apply hn3
      rw [hnqy, this]
      exact dvd_mul_left 3 y
  have hqx2 : 2 ≤ qx := by omega
  have hqz5 : 5 ≤ qz := by omega
  have h2x : 2 * x ≤ n := calc
    2 * x ≤ qx * x := Nat.mul_le_mul_right x hqx2
    _ = x * qx := by ac_rfl
    _ = n := hnqx.symm
  have h4y : 4 * y ≤ n := calc
    4 * y ≤ qy * y := Nat.mul_le_mul_right y hqy4
    _ = y * qy := by ac_rfl
    _ = n := hnqy.symm
  have h5z : 5 * z ≤ n := calc
    5 * z ≤ qz * z := Nat.mul_le_mul_right z hqz5
    _ = z * qz := by ac_rfl
    _ = n := hnqz.symm
  rw [hstep]
  omega

private lemma properDivisor_of_eq_mul {n d q : ℕ} (hd : 0 < d) (hq : 1 < q)
    (h : n = d * q) : d ∈ Nat.properDivisors n := by
  have hn : n ≠ 0 := by rw [h]; positivity
  exact (Nat.mem_properDivisors_iff_exists hn).2 ⟨q, hq, h⟩

private lemma step_of_cofactor_two_three {n x : ℕ} (hx : 0 < x)
    (hn : n = 6 * x) (h4 : ¬4 ∣ n) (h5 : ¬5 ∣ n) : step n = n := by
  have hxmem : 3 * x ∈ Nat.properDivisors n := by
    apply properDivisor_of_eq_mul (q := 2) (by positivity) (by norm_num)
    rw [hn]
    omega
  have hymem : 2 * x ∈ Nat.properDivisors n := by
    apply properDivisor_of_eq_mul (q := 3) (by positivity) (by norm_num)
    rw [hn]
    omega
  have hzmem : x ∈ Nat.properDivisors n := by
    apply properDivisor_of_eq_mul (q := 6) hx (by norm_num)
    rw [hn]
    omega
  have hresult := step_eq_of_three_largest hxmem hymem (by omega) hzmem (by omega) (by omega)
  exact hresult (by
    intro d hd
    obtain ⟨q, hq, hnq⟩ :=
      (Nat.mem_properDivisors_iff_exists (by omega : n ≠ 0)).mp hd
    have hq2 : 2 ≤ q := by omega
    have : 2 * d ≤ n := calc
      2 * d ≤ q * d := Nat.mul_le_mul_right d hq2
      _ = d * q := by ac_rfl
      _ = n := hnq.symm
    rw [hn] at this
    omega) (by
    intro d hd hdx
    obtain ⟨q, hq, hnq⟩ :=
      (Nat.mem_properDivisors_iff_exists (by omega : n ≠ 0)).mp hd
    have hq3 : 3 ≤ q := by
      by_contra h
      have : q = 2 := by omega
      rw [this, hn] at hnq
      omega
    have : 3 * d ≤ n := calc
      3 * d ≤ q * d := Nat.mul_le_mul_right d hq3
      _ = d * q := by ac_rfl
      _ = n := hnq.symm
    rw [hn] at this
    omega) (by
    intro d hd hdx hdy
    obtain ⟨q, hq, hnq⟩ :=
      (Nat.mem_properDivisors_iff_exists (by omega : n ≠ 0)).mp hd
    have hq6 : 6 ≤ q := by
      by_contra h
      have hcases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · rw [hn] at hnq
        omega
      · rw [hn] at hnq
        omega
      · apply h4
        refine ⟨d, ?_⟩
        rw [hnq]
        omega
      · apply h5
        refine ⟨d, ?_⟩
        rw [hnq]
        omega
    have : 6 * d ≤ n := calc
      6 * d ≤ q * d := Nat.mul_le_mul_right d hq6
      _ = d * q := by ac_rfl
      _ = n := hnq.symm
    rw [hn] at this
    omega) |>.trans (by omega)

private lemma step_of_twelve_dvd {n t : ℕ} (ht : 0 < t) (hn : n = 12 * t) :
    step n = 13 * t := by
  have hxmem : 6 * t ∈ Nat.properDivisors n := by
    apply properDivisor_of_eq_mul (q := 2) (by positivity) (by norm_num)
    rw [hn]
    omega
  have hymem : 4 * t ∈ Nat.properDivisors n := by
    apply properDivisor_of_eq_mul (q := 3) (by positivity) (by norm_num)
    rw [hn]
    omega
  have hzmem : 3 * t ∈ Nat.properDivisors n := by
    apply properDivisor_of_eq_mul (q := 4) (by positivity) (by norm_num)
    rw [hn]
    omega
  have hstep := step_eq_of_three_largest hxmem hymem (by omega) hzmem (by omega) (by omega)
  have heq := hstep (by
    intro d hd
    obtain ⟨q, hq, hnq⟩ :=
      (Nat.mem_properDivisors_iff_exists (by omega : n ≠ 0)).mp hd
    have hq2 : 2 ≤ q := by omega
    have : 2 * d ≤ n := calc
      2 * d ≤ q * d := Nat.mul_le_mul_right d hq2
      _ = d * q := by ac_rfl
      _ = n := hnq.symm
    rw [hn] at this
    omega) (by
    intro d hd hdx
    obtain ⟨q, hq, hnq⟩ :=
      (Nat.mem_properDivisors_iff_exists (by omega : n ≠ 0)).mp hd
    have hq3 : 3 ≤ q := by
      by_contra h
      have : q = 2 := by omega
      rw [this, hn] at hnq
      omega
    have : 3 * d ≤ n := calc
      3 * d ≤ q * d := Nat.mul_le_mul_right d hq3
      _ = d * q := by ac_rfl
      _ = n := hnq.symm
    rw [hn] at this
    omega) (by
    intro d hd hdx hdy
    obtain ⟨q, hq, hnq⟩ :=
      (Nat.mem_properDivisors_iff_exists (by omega : n ≠ 0)).mp hd
    have hq4 : 4 ≤ q := by
      by_contra h
      have : q = 2 ∨ q = 3 := by omega
      rcases this with rfl | rfl <;> rw [hn] at hnq <;> omega
    have : 4 * d ≤ n := calc
      4 * d ≤ q * d := Nat.mul_le_mul_right d hq4
      _ = d * q := by ac_rfl
      _ = n := hnq.symm
    rw [hn] at this
    omega)
  omega

private lemma admissible_six_mul {m : ℕ} (hm : 0 < m) : Admissible (6 * m) := by
  constructor
  · positivity
  · have h₁ : m ∈ Nat.properDivisors (6 * m) := by
      apply properDivisor_of_eq_mul (q := 6) hm (by norm_num)
      omega
    have h₂ : 2 * m ∈ Nat.properDivisors (6 * m) := by
      apply properDivisor_of_eq_mul (q := 3) (by positivity) (by norm_num)
      omega
    have h₃ : 3 * m ∈ Nat.properDivisors (6 * m) := by
      apply properDivisor_of_eq_mul (q := 2) (by positivity) (by norm_num)
      omega
    have hsub : {m, 2 * m, 3 * m} ⊆ Nat.properDivisors (6 * m) := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · exact h₃
    have hcard3 : #{m, 2 * m, 3 * m} = 3 := by
      have hne1 : m ≠ 2 * m := by omega
      have hne2 : m ≠ 3 * m := by omega
      have hne3 : 2 * m ≠ 3 * m := by omega
      simp [hne1, hne2, hne3]
    calc
      3 = #{m, 2 * m, 3 * m} := hcard3.symm
      _ ≤ #(Nat.properDivisors (6 * m)) := Finset.card_le_card hsub

private lemma four_not_dvd_six_mul_of_odd {m : ℕ} (hm : Odd m) : ¬4 ∣ 6 * m := by
  intro h
  rcases hm with ⟨r, hr⟩
  obtain ⟨q, hq⟩ := h
  omega


private lemma five_not_dvd_six_mul {m : ℕ} (hm : ¬5 ∣ m) : ¬5 ∣ 6 * m := by
  exact Nat.prime_five.not_dvd_mul (by norm_num) hm

private lemma answer_admissible {n : ℕ} (hn : n ∈ answer) : Admissible n := by
  obtain ⟨k, m, rfl, hm, h5⟩ := hn
  rw [show 6 * 12 ^ k * m = 6 * (12 ^ k * m) by ring]
  apply admissible_six_mul
  exact Nat.mul_pos (by positivity) hm.pos

private lemma step_mem_answer {n : ℕ} (hn : n ∈ answer) : step n ∈ answer := by
  obtain ⟨k, m, hn, hm, h5⟩ := hn
  subst n
  cases k with
  | zero =>
      have hmpos : 0 < m := hm.pos
      have h4 : ¬4 ∣ 6 * 12 ^ 0 * m := by
        simpa using four_not_dvd_six_mul_of_odd hm
      have h5n : ¬5 ∣ 6 * 12 ^ 0 * m := by
        simpa using five_not_dvd_six_mul h5
      have hstep : step (6 * 12 ^ 0 * m) = 6 * m := by
        simpa using step_of_cofactor_two_three hmpos (n := 6 * m) (x := m) rfl
          (by simpa using h4) (by simpa using h5n)
      rw [hstep]
      exact ⟨0, m, by simp, hm, h5⟩
  | succ k =>
      let t := 6 * 12 ^ k * m
      have htpos : 0 < t := by
        dsimp [t]
        exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) k)) hm.pos
      have hn12 : 6 * 12 ^ (k + 1) * m = 12 * t := by
        dsimp [t]
        rw [pow_succ]
        ring
      have hstep : step (6 * 12 ^ (k + 1) * m) = 13 * t := by
        rw [hn12]
        exact step_of_twelve_dvd htpos rfl
      rw [hstep]
      refine ⟨k, 13 * m, ?_, (by exact (by norm_num : Odd 13).mul hm), ?_⟩
      · dsimp [t]
        ring
      · exact Nat.prime_five.not_dvd_mul (by norm_num) h5

private lemma exists_orbit_of_answer {n : ℕ} (hn : n ∈ answer) :
    ∃ a : ℕ → ℕ, a 0 = n ∧ ∀ i, Admissible (a i) ∧ a (i + 1) = step (a i) := by
  let a : ℕ → ℕ := fun i => step^[i] n
  have ha : ∀ i, a i ∈ answer := by
    intro i
    induction i with
    | zero => simpa [a] using hn
    | succ i ih =>
        rw [show a (i + 1) = step (a i) by
          simp only [a, Function.iterate_succ_apply']]
        exact step_mem_answer ih
  refine ⟨a, by simp [a], ?_⟩
  intro i
  refine ⟨answer_admissible (ha i), ?_⟩
  simp only [a, Function.iterate_succ_apply']

private lemma six_dvd_all_of_orbit (a : ℕ → ℕ)
    (ha : ∀ i, Admissible (a i) ∧ a (i + 1) = step (a i)) :
    ∀ i, 6 ∣ a i := by
  -- Outside the multiples of six, `step` preserves that condition and strictly decreases.
  -- An infinite positive orbit therefore cannot ever enter this descending region.
  intro i
  by_contra hi
  have hnot : ∀ r, ¬6 ∣ a (i + r) := by
    intro r
    induction r with
    | zero => simpa using hi
    | succ r ih =>
        have hpres := not_six_dvd_step (ha (i + r)).1.1 (ha (i + r)).1.2 ih
        rw [show i + (r + 1) = (i + r) + 1 by omega, (ha (i + r)).2]
        exact hpres
  have hdesc : ∀ r, a (i + (r + 1)) < a (i + r) := by
    intro r
    have hlt := step_lt_of_not_six_dvd (ha (i + r)).1.1 (ha (i + r)).1.2 (hnot r)
    rw [show i + (r + 1) = (i + r) + 1 by omega, (ha (i + r)).2]
    exact hlt
  have hbound : ∀ r, a (i + r) + r ≤ a i := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        have hlt := hdesc r
        omega
  have := hbound (a i + 1)
  omega

private lemma step_of_thirty_mul {t : ℕ} (ht : 0 < t) (h4 : ¬4 ∣ 30 * t) :
    step (30 * t) = 31 * t := by
  have hxmem : 15 * t ∈ Nat.properDivisors (30 * t) := by
    apply properDivisor_of_eq_mul (q := 2) (by positivity) (by norm_num)
    omega
  have hymem : 10 * t ∈ Nat.properDivisors (30 * t) := by
    apply properDivisor_of_eq_mul (q := 3) (by positivity) (by norm_num)
    omega
  have hzmem : 6 * t ∈ Nat.properDivisors (30 * t) := by
    apply properDivisor_of_eq_mul (q := 5) (by positivity) (by norm_num)
    omega
  have hresult := step_eq_of_three_largest hxmem hymem (by omega) hzmem (by omega) (by omega)
  have heq := hresult (by
    intro d hd
    obtain ⟨q, hq, hnq⟩ :=
      (Nat.mem_properDivisors_iff_exists (by positivity : 30 * t ≠ 0)).mp hd
    have hq2 : 2 ≤ q := by omega
    have : 2 * d ≤ 30 * t := calc
      2 * d ≤ q * d := Nat.mul_le_mul_right d hq2
      _ = d * q := by ac_rfl
      _ = 30 * t := hnq.symm
    omega) (by
    intro d hd hdx
    obtain ⟨q, hq, hnq⟩ :=
      (Nat.mem_properDivisors_iff_exists (by positivity : 30 * t ≠ 0)).mp hd
    have hq3 : 3 ≤ q := by
      by_contra h
      have : q = 2 := by omega
      rw [this] at hnq
      omega
    have : 3 * d ≤ 30 * t := calc
      3 * d ≤ q * d := Nat.mul_le_mul_right d hq3
      _ = d * q := by ac_rfl
      _ = 30 * t := hnq.symm
    omega) (by
    intro d hd hdx hdy
    obtain ⟨q, hq, hnq⟩ :=
      (Nat.mem_properDivisors_iff_exists (by positivity : 30 * t ≠ 0)).mp hd
    have hq5 : 5 ≤ q := by
      by_contra h
      have hcases : q = 2 ∨ q = 3 ∨ q = 4 := by omega
      rcases hcases with rfl | rfl | rfl
      · have hd' : d = 15 * t := by omega
        exact hdx hd'
      · have hd' : d = 10 * t := by omega
        exact hdy hd'
      · exact (h4 ⟨d, by omega⟩).elim
    have : 5 * d ≤ 30 * t := calc
      5 * d ≤ q * d := Nat.mul_le_mul_right d hq5
      _ = d * q := by ac_rfl
      _ = 30 * t := hnq.symm
    omega)
  omega

private lemma iterate_step_answer_core (e m : ℕ) (hm : 0 < m) :
    step^[e] (6 * 12 ^ e * m) = 6 * 13 ^ e * m := by
  induction e generalizing m with
  | zero => simp
  | succ e ih =>
      have htpos : 0 < 6 * 12 ^ e * m := by positivity
      have hfirst : step (6 * 12 ^ (e + 1) * m) = 6 * 12 ^ e * (13 * m) := by
        have heq : 6 * 12 ^ (e + 1) * m = 12 * (6 * 12 ^ e * m) := by
          rw [pow_succ]
          ring
        rw [heq, step_of_twelve_dvd htpos rfl]
        ring
      rw [Function.iterate_succ_apply, hfirst, ih (13 * m) (by positivity)]
      rw [pow_succ]
      ring

private lemma orbit_eq_iterate (a : ℕ → ℕ)
    (ha : ∀ i, a (i + 1) = step (a i)) : ∀ i, a i = step^[i] (a 0) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      rw [ha i, ih, Function.iterate_succ_apply']

private lemma orbit_initial_in_answer (a : ℕ → ℕ)
    (ha : ∀ i, Admissible (a i) ∧ a (i + 1) = step (a i)) : a 0 ∈ answer := by
  -- Remove the largest power of 12 from `a 0 / 6`. Each removed factor advances
  -- by `12t ↦ 13t`; divisibility by six at the following term then forces the
  -- remaining factor to be odd and not divisible by five.
  have h6all := six_dvd_all_of_orbit a ha
  let e := padicValNat 12 (a 0 / 6)
  let m := Nat.divMaxPow (a 0 / 6) 12
  have ha0pos : 0 < a 0 := (ha 0).1.1
  have hqpos : 0 < a 0 / 6 := Nat.div_pos (Nat.le_of_dvd ha0pos (h6all 0)) (by norm_num)
  have hmpos : 0 < m := by
    have hprod := Nat.divMaxPow_mul_pow_padicValNat 12 (a 0 / 6)
    change m * 12 ^ e = a 0 / 6 at hprod
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    rw [hm0, zero_mul] at hprod
    exact (Nat.ne_of_gt hqpos) hprod.symm
  have hm12 : ¬12 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) (Nat.ne_of_gt hqpos)
  have ha0eq : a 0 = 6 * 12 ^ e * m := by
    have hdecomp := Nat.divMaxPow_mul_pow_padicValNat 12 (a 0 / 6)
    rw [show a 0 = 6 * (a 0 / 6) by exact (Nat.mul_div_cancel' (h6all 0)).symm,
      ← hdecomp]
    dsimp [e, m]
    ring
  have haeeq : a e = 6 * 13 ^ e * m := by
    rw [orbit_eq_iterate a (fun i => (ha i).2), ha0eq]
    exact iterate_step_answer_core e m hmpos
  have hmodd : Odd m := by
    apply Nat.not_even_iff_odd.mp
    intro hmeven
    have hm2 : 2 ∣ m := even_iff_two_dvd.mp hmeven
    obtain ⟨r, hr⟩ := hm2
    have hrpos : 0 < r := by rw [hr] at hmpos; omega
    have hnext := (ha e).2
    have haetwelve : a e = 12 * (13 ^ e * r) := by rw [haeeq, hr]; ring
    rw [haetwelve] at hnext
    rw [step_of_twelve_dvd (n := 12 * (13 ^ e * r)) (t := 13 ^ e * r) (by positivity) rfl] at hnext
    have h6next : 6 ∣ 13 * (13 ^ e * r) := by rw [← hnext]; exact h6all (e + 1)
    have hcop13 : Nat.Coprime 6 (13 ^ (e + 1)) :=
      Nat.Coprime.pow_right (e + 1) (by norm_num)
    have h6r : 6 ∣ r := by
      apply hcop13.dvd_of_dvd_mul_left
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h6next
    obtain ⟨s, hs⟩ := h6r
    apply hm12
    refine ⟨s, ?_⟩
    rw [hr, hs]
    omega
  have hm5 : ¬5 ∣ m := by
    intro hm5
    obtain ⟨r, hr⟩ := hm5
    have hrpos : 0 < r := by rw [hr] at hmpos; omega
    have hrodd : Odd r := Odd.of_dvd_nat hmodd ⟨5, by simpa [mul_comm] using hr⟩
    have htodd : Odd (13 ^ e * r) := ((by norm_num : Odd 13).pow).mul hrodd
    have hnext := (ha e).2
    have hae30 : a e = 30 * (13 ^ e * r) := by rw [haeeq, hr]; ring
    have h4 : ¬4 ∣ 30 * (13 ^ e * r) := by
      simpa [show 30 * (13 ^ e * r) = 6 * (5 * (13 ^ e * r)) by ring] using
        four_not_dvd_six_mul_of_odd ((by norm_num : Odd 5).mul htodd)
    rw [hae30, step_of_thirty_mul (by positivity) h4] at hnext
    have h6next : 6 ∣ 31 * (13 ^ e * r) := by rw [← hnext]; exact h6all (e + 1)
    have hoddnext : Odd (31 * (13 ^ e * r)) := (by norm_num : Odd 31).mul htodd
    exact Nat.not_even_iff_odd.mpr hoddnext (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 6).trans h6next))
  exact ⟨e, m, ha0eq, hmodd, hm5⟩

theorem imo2025_p4 :
    {a₁ | ∃ a : ℕ → ℕ, a 0 = a₁ ∧ ∀ i,
      0 < a i ∧ 3 ≤ #(Nat.properDivisors (a i)) ∧
        a (i + 1) = (((Nat.properDivisors (a i)).sort (· ≤ ·)).reverse.take 3).sum} =
      answer := by
  ext n
  constructor
  · rintro ⟨a, rfl, ha⟩
    apply orbit_initial_in_answer a
    intro i
    exact ⟨⟨(ha i).1, (ha i).2.1⟩, by simpa [step] using (ha i).2.2⟩
  · intro hn
    obtain ⟨a, ha0, ha⟩ := exists_orbit_of_answer hn
    refine ⟨a, ha0, ?_⟩
    intro i
    exact ⟨(ha i).1.1, (ha i).1.2, by simpa [step] using (ha i).2⟩

end IMO2025P4
