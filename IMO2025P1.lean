import Mathlib

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace IMO2025P1

abbrev Point := ℝ × ℝ
abbrev Line := Set Point

def affineLine (A B C : ℝ) : Line :=
  {v : Point | A * v.1 + B * v.2 + C = 0}

def OnLine (l : Line) (a b : ℕ) : Prop :=
  ((a : ℝ), (b : ℝ)) ∈ l

def IsAffineLine (l : Line) : Prop :=
  ∃ A B C : ℝ, ¬(A = 0 ∧ B = 0) ∧ l = affineLine A B C

def IsSpecial (l : Line) : Prop :=
  ∃ A B C : ℝ, l = affineLine A B C ∧ A ≠ 0 ∧ B ≠ 0 ∧ A ≠ B

def Covers (n : ℕ) (lines : Finset Line) : Prop :=
  ∀ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b ≤ n + 1 →
    ∃ l ∈ lines, OnLine l a b

def vertical : Line := affineLine 1 0 (-1)

def horizontal : Line := affineLine 0 1 (-1)

def diagonal (n : ℕ) : Line := affineLine 1 1 (-(n : ℝ) - 1)

lemma vertical_eq_of_two {l : Line} (hl : IsAffineLine l)
    {p q : ℕ} (hpq : p ≠ q) (hp : OnLine l 1 p) (hq : OnLine l 1 q) :
    l = vertical := by
  rcases hl with ⟨A, B, C, hnz, hline⟩
  subst l
  simp only [OnLine, affineLine, Set.mem_setOf_eq, Nat.cast_one] at hp hq
  have hpqr : (p : ℝ) ≠ (q : ℝ) := by exact_mod_cast hpq
  have hB : B = 0 := by
    by_contra hB
    have hmul : B * (p : ℝ) = B * (q : ℝ) := by linarith
    exact hpqr (mul_left_cancel₀ hB hmul)
  have hA : A ≠ 0 := by aesop
  have hAC : A + C = 0 := by simpa [hB] using hp
  apply Set.ext
  intro v
  simp only [affineLine, vertical, Set.mem_setOf_eq]
  norm_num
  constructor
  · intro h
    have hv : v.1 = 1 := by
      apply mul_left_cancel₀ hA
      rw [hB, zero_mul] at h
      nlinarith
    linarith
  · intro h
    have hv : v.1 = 1 := by linarith
    rw [hB, zero_mul, hv]
    linarith

lemma horizontal_eq_of_two {l : Line} (hl : IsAffineLine l)
    {p q : ℕ} (hpq : p ≠ q) (hp : OnLine l p 1) (hq : OnLine l q 1) :
    l = horizontal := by
  rcases hl with ⟨A, B, C, hnz, hline⟩
  subst l
  simp only [OnLine, affineLine, Set.mem_setOf_eq, Nat.cast_one] at hp hq
  have hpqr : (p : ℝ) ≠ (q : ℝ) := by exact_mod_cast hpq
  have hA : A = 0 := by
    by_contra hA
    have hmul : A * (p : ℝ) = A * (q : ℝ) := by linarith
    exact hpqr (mul_left_cancel₀ hA hmul)
  have hB : B ≠ 0 := by aesop
  have hBC : B + C = 0 := by simpa [hA] using hp
  apply Set.ext
  intro v
  simp only [affineLine, horizontal, Set.mem_setOf_eq]
  norm_num
  constructor
  · intro h
    have hv : v.2 = 1 := by
      apply mul_left_cancel₀ hB
      rw [hA, zero_mul, zero_add] at h
      nlinarith
    linarith
  · intro h
    have hv : v.2 = 1 := by linarith
    rw [hA, zero_mul, zero_add, hv]
    linarith

lemma diagonal_eq_of_two {n : ℕ} {l : Line} (hl : IsAffineLine l)
    {p q : ℕ} (hpq : p ≠ q) (hp : OnLine l p (n + 1 - p))
    (hq : OnLine l q (n + 1 - q)) (hp_le : p ≤ n + 1) (hq_le : q ≤ n + 1) :
    l = diagonal n := by
  rcases hl with ⟨A, B, C, hnz, hline⟩
  subst l
  simp only [OnLine, affineLine, Set.mem_setOf_eq] at hp hq
  rw [Nat.cast_sub hp_le] at hp
  rw [Nat.cast_sub hq_le] at hq
  norm_num at hp hq
  have hpqr : (p : ℝ) ≠ (q : ℝ) := by exact_mod_cast hpq
  have hAB : A = B := by
    by_contra hAB
    have hne : A - B ≠ 0 := sub_ne_zero.mpr hAB
    have hmul : (A - B) * (p : ℝ) = (A - B) * (q : ℝ) := by nlinarith
    exact hpqr (mul_left_cancel₀ hne hmul)
  have hA : A ≠ 0 := by aesop
  subst B
  have hC : A * ((n : ℝ) + 1) + C = 0 := by
    nlinarith
  apply Set.ext
  intro v
  simp only [affineLine, diagonal, Set.mem_setOf_eq]
  norm_num
  constructor
  · intro h
    apply mul_left_cancel₀ hA
    calc
      A * (v.1 + v.2 + (-(n : ℝ) - 1)) =
          A * v.1 + A * v.2 + C := by nlinarith [hC]
      _ = 0 := h
      _ = A * 0 := by ring
  · intro h
    have hsum : v.1 + v.2 = (n : ℝ) + 1 := by linarith
    calc
      A * v.1 + A * v.2 + C = A * (v.1 + v.2) + C := by ring
      _ = A * ((n : ℝ) + 1) + C := by rw [hsum]
      _ = 0 := hC

lemma determinant_eq_zero {l : Line} (hl : IsAffineLine l)
    {x₁ y₁ x₂ y₂ x₃ y₃ : ℝ}
    (h₁ : (x₁, y₁) ∈ l) (h₂ : (x₂, y₂) ∈ l) (h₃ : (x₃, y₃) ∈ l) :
    (x₂ - x₁) * (y₃ - y₁) - (y₂ - y₁) * (x₃ - x₁) = 0 := by
  rcases hl with ⟨A, B, C, hnz, hline⟩
  subst l
  simp only [affineLine, Set.mem_setOf_eq] at h₁ h₂ h₃
  have h₁₂ : A * (x₂ - x₁) + B * (y₂ - y₁) = 0 := by linarith
  have h₁₃ : A * (x₃ - x₁) + B * (y₃ - y₁) = 0 := by linarith
  by_cases hA : A = 0
  · have hB : B ≠ 0 := by aesop
    have hy₁₂ : B * (y₂ - y₁) = 0 := by simpa [hA] using h₁₂
    have hy₁₃ : B * (y₃ - y₁) = 0 := by simpa [hA] using h₁₃
    have hy₁₂' : y₂ - y₁ = 0 := (mul_eq_zero.mp hy₁₂).resolve_left hB
    have hy₁₃' : y₃ - y₁ = 0 := (mul_eq_zero.mp hy₁₃).resolve_left hB
    rw [hy₁₂', hy₁₃']
    ring
  · have hx₁₂ : A * (x₂ - x₁) = -B * (y₂ - y₁) := by linarith
    have hx₁₃ : A * (x₃ - x₁) = -B * (y₃ - y₁) := by linarith
    apply mul_left_cancel₀ hA
    calc
      A * ((x₂ - x₁) * (y₃ - y₁) - (y₂ - y₁) * (x₃ - x₁)) =
          (A * (x₂ - x₁)) * (y₃ - y₁) - (y₂ - y₁) * (A * (x₃ - x₁)) := by ring
      _ = (-B * (y₂ - y₁)) * (y₃ - y₁) - (y₂ - y₁) * (-B * (y₃ - y₁)) := by
        rw [hx₁₂, hx₁₃]
      _ = 0 := by ring
      _ = A * 0 := by ring

lemma vertex_of_three_side_points {n : ℕ} {l : Line} (hl : IsAffineLine l)
    {p q r : ℝ} (hp : 0 ≤ p) (hpn : p ≤ (n : ℝ))
    (hq : 0 ≤ q) (hqn : q ≤ (n : ℝ)) (hr : 0 ≤ r) (hrn : r ≤ (n : ℝ))
    (h₁ : ((1 : ℝ), p + 1) ∈ l) (h₂ : (q + 1, (1 : ℝ)) ∈ l)
    (h₃ : (r + 1, (n : ℝ) - r + 1) ∈ l) :
    ((1 : ℝ), (1 : ℝ)) ∈ l ∨ ((1 : ℝ), (n : ℝ) + 1) ∈ l ∨
      ((n : ℝ) + 1, (1 : ℝ)) ∈ l := by
  by_contra H
  push Not at H
  have hp0 : 0 < p := by
    rcases lt_or_eq_of_le hp with h | h
    · exact h
    · subst p
      apply False.elim
      apply H.1
      simpa using h₁
  have hq0 : 0 < q := by
    rcases lt_or_eq_of_le hq with h | h
    · exact h
    · subst q
      apply False.elim
      apply H.1
      simpa using h₂
  have hr0 : 0 < r := by
    rcases lt_or_eq_of_le hr with h | h
    · exact h
    · subst r
      apply False.elim
      apply H.2.1
      simpa using h₃
  have hpn' : p < (n : ℝ) := by
    rcases lt_or_eq_of_le hpn with h | h
    · exact h
    · subst p
      apply False.elim
      apply H.2.1
      simpa using h₁
  have hqn' : q < (n : ℝ) := by
    rcases lt_or_eq_of_le hqn with h | h
    · exact h
    · subst q
      apply False.elim
      apply H.2.2
      simpa using h₂
  have hrn' : r < (n : ℝ) := by
    rcases lt_or_eq_of_le hrn with h | h
    · exact h
    · subst r
      apply False.elim
      apply H.2.2
      simpa using h₃
  have hcol := determinant_eq_zero hl h₁ h₂ h₃
  have hzero : q * ((n : ℝ) - r - p) + p * r = 0 := by
    ring_nf at hcol ⊢
    linarith [hcol]
  have hid : (n : ℝ) * (q * ((n : ℝ) - r - p) + p * r) =
      r * p * ((n : ℝ) - q) + q * ((n : ℝ) - r) * ((n : ℝ) - p) := by ring
  have hnq : 0 < (n : ℝ) - q := by linarith
  have hnr : 0 < (n : ℝ) - r := by linarith
  have hnp : 0 < (n : ℝ) - p := by linarith
  have hrp : 0 < r * p := mul_pos hr0 hp0
  have hqr : 0 < q * ((n : ℝ) - r) := mul_pos hq0 hnr
  have hpos1 : 0 < r * p * ((n : ℝ) - q) := mul_pos hrp hnq
  have hpos2 : 0 < q * ((n : ℝ) - r) * ((n : ℝ) - p) := mul_pos hqr hnp
  have hleft : (n : ℝ) * (q * ((n : ℝ) - r - p) + p * r) = 0 := by
    rw [hzero]
    ring
  have hsum : r * p * ((n : ℝ) - q) + q * ((n : ℝ) - r) * ((n : ℝ) - p) = 0 := by
    rw [← hid]
    exact hleft
  nlinarith

lemma nonspecial_pair {l : Line} (hl : IsAffineLine l) (hns : ¬IsSpecial l)
    {p q r s : ℕ} (hp : OnLine l p q) (hr : OnLine l r s) :
    p = r ∨ q = s ∨ p + q = r + s := by
  rcases hl with ⟨A, B, C, hnz, hline⟩
  subst l
  simp only [OnLine, affineLine, Set.mem_setOf_eq] at hp hr
  have hside : A = 0 ∨ B = 0 ∨ A = B := by
    by_contra h
    push Not at h
    apply hns
    exact ⟨A, B, C, rfl, h.1, h.2.1, h.2.2⟩
  rcases hside with hA | hB | hAB
  · right
    left
    have hBn : B ≠ 0 := by aesop
    have hmul : B * (q : ℝ) = B * (s : ℝ) := by
      subst A
      linarith
    have hcast := mul_left_cancel₀ hBn hmul
    exact_mod_cast hcast
  · left
    have hAn : A ≠ 0 := by aesop
    have hmul : A * (p : ℝ) = A * (r : ℝ) := by
      subst B
      linarith
    have hcast := mul_left_cancel₀ hAn hmul
    exact_mod_cast hcast
  · right
    right
    subst B
    have hAn : A ≠ 0 := by aesop
    have hmul : A * ((p : ℝ) + (q : ℝ)) = A * ((r : ℝ) + (s : ℝ)) := by
      nlinarith [hp, hr]
    have hcast := mul_left_cancel₀ hAn hmul
    exact_mod_cast hcast

lemma affineLine_special {A B C : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B) :
    IsSpecial (affineLine A B C) :=
  ⟨A, B, C, rfl, hA, hB, hAB⟩

lemma special_same_x_false {l : Line} (hsp : IsSpecial l)
    {x y z : ℕ} (hyz : y ≠ z) (hy : OnLine l x y) (hz : OnLine l x z) : False := by
  rcases hsp with ⟨A, B, C, hline, hA, hB, hAB⟩
  subst l
  simp only [OnLine, affineLine, Set.mem_setOf_eq] at hy hz
  have hmul : B * (y : ℝ) = B * (z : ℝ) := by linarith
  have hcast : (y : ℝ) = (z : ℝ) := mul_left_cancel₀ hB hmul
  exact hyz (by exact_mod_cast hcast)

lemma special_same_y_false {l : Line} (hsp : IsSpecial l)
    {x y z : ℕ} (hyz : y ≠ z) (hy : OnLine l y x) (hz : OnLine l z x) : False := by
  rcases hsp with ⟨A, B, C, hline, hA, hB, hAB⟩
  subst l
  simp only [OnLine, affineLine, Set.mem_setOf_eq] at hy hz
  have hmul : A * (y : ℝ) = A * (z : ℝ) := by linarith
  have hcast : (y : ℝ) = (z : ℝ) := mul_left_cancel₀ hA hmul
  exact hyz (by exact_mod_cast hcast)

lemma special_same_sum_false {l : Line} (hsp : IsSpecial l)
    {x y z w : ℕ} (hne : (x, y) ≠ (z, w)) (hsum : x + y = z + w)
    (hxy : OnLine l x y) (hzw : OnLine l z w) : False := by
  rcases hsp with ⟨A, B, C, hline, hA, hB, hAB⟩
  subst l
  simp only [OnLine, affineLine, Set.mem_setOf_eq] at hxy hzw
  have hxz : x ≠ z := by
    intro hxz
    apply hne
    apply Prod.ext hxz
    omega
  have hsumR : (x : ℝ) + y = (z : ℝ) + w := by exact_mod_cast hsum
  have hmul : (A - B) * (x : ℝ) = (A - B) * (z : ℝ) := by
    have heq1 : A * ((x : ℝ) - z) + B * ((y : ℝ) - w) = 0 := by
      linarith [hxy, hzw]
    have heq2 : ((y : ℝ) - w) = -((x : ℝ) - z) := by
      linarith [hsumR]
    rw [heq2] at heq1
    nlinarith [heq1]
  have hcast : (x : ℝ) = (z : ℝ) :=
    mul_left_cancel₀ (sub_ne_zero.mpr hAB) hmul
  exact hxz (by exact_mod_cast hcast)

lemma vertical_not_special : ¬IsSpecial vertical := by
  rintro ⟨A, B, D, hline, hA, hB, hAB⟩
  have hp := Set.ext_iff.mp hline ((-D / A : ℝ), (0 : ℝ))
  have hp2 := Set.ext_iff.mp hline ((-D / A : ℝ), (1 : ℝ))
  simp only [vertical, affineLine, Set.mem_setOf_eq] at hp hp2
  have hr : A * (-D / A) + D = 0 := by
    rw [div_eq_mul_inv]
    calc
      A * (-D * A⁻¹) + D = -(D * (A * A⁻¹)) + D := by ring
      _ = -(D * 1) + D := by rw [mul_inv_cancel₀ hA]
      _ = 0 := by ring
  have hx := hp.mpr (show A * (-D / A) + B * 0 + D = 0 by linarith)
  have hx2 := hp2.mp (show 1 * (-D / A) + 0 * 1 - 1 = 0 by linarith)
  have hzero : B = 0 := by nlinarith [hr, hx2]
  exact hB hzero

lemma horizontal_not_special : ¬IsSpecial horizontal := by
  rintro ⟨A, B, D, hline, hA, hB, hAB⟩
  have hp := Set.ext_iff.mp hline ((0 : ℝ), (-D / B : ℝ))
  have hp2 := Set.ext_iff.mp hline ((1 : ℝ), (-D / B : ℝ))
  simp only [horizontal, affineLine, Set.mem_setOf_eq] at hp hp2
  have hr : B * (-D / B) + D = 0 := by
    rw [div_eq_mul_inv]
    calc
      B * (-D * B⁻¹) + D = -(D * (B * B⁻¹)) + D := by ring
      _ = -(D * 1) + D := by rw [mul_inv_cancel₀ hB]
      _ = 0 := by ring
  have hx := hp.mpr (show A * 0 + B * (-D / B) + D = 0 by linarith)
  have hx2 := hp2.mp (show 0 * 1 + 1 * (-D / B) - 1 = 0 by linarith)
  have hzero : A = 0 := by nlinarith [hr, hx2]
  exact hA hzero

lemma diagonal_affineLine_not_special (C : ℝ) : ¬IsSpecial (affineLine 1 1 C) := by
  rintro ⟨A, B, D, hline, hA, hB, hAB⟩
  have hp := Set.ext_iff.mp hline ((0 : ℝ), (-D / B : ℝ))
  have hp2 := Set.ext_iff.mp hline ((1 : ℝ), (-D / B - 1 : ℝ))
  simp only [affineLine, Set.mem_setOf_eq] at hp hp2
  have hr : B * (-D / B) + D = 0 := by
    rw [div_eq_mul_inv]
    calc
      B * (-D * B⁻¹) + D = -(D * (B * B⁻¹)) + D := by ring
      _ = -(D * 1) + D := by rw [mul_inv_cancel₀ hB]
      _ = 0 := by ring
  have hx := hp.mpr (show A * 0 + B * (-D / B) + D = 0 by linarith)
  have hleft : 1 + (-D / B - 1) + C = 0 := by
    have := hp.mp (by simpa using hx)
    nlinarith
  have hx2 := hp2.mp (show 1 * 1 + 1 * (-D / B - 1) + C = 0 by nlinarith [hleft])
  have heq : A = B := by nlinarith [hr, hx2]
  exact hAB heq

lemma diagonal_not_special (n : ℕ) : ¬IsSpecial (diagonal n) := by
  exact diagonal_affineLine_not_special (-(n : ℝ) - 1)

def BoundaryPoint (n : ℕ) (p : ℕ × ℕ) : Prop :=
  (1 ≤ p.1 ∧ p.1 ≤ n ∧ p.2 = 1) ∨
  (p.1 = 1 ∧ 2 ≤ p.2 ∧ p.2 ≤ n) ∨
  (2 ≤ p.1 ∧ p.1 ≤ n - 1 ∧ p.2 = n + 1 - p.1)

def boundary (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter (BoundaryPoint n)

lemma mem_boundary {n a b : ℕ} : (a, b) ∈ boundary n ↔ BoundaryPoint n (a, b) := by
  classical
  simp only [boundary, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with h | h | h <;> simp_all <;> omega

lemma boundary_triangle {n a b : ℕ} (h : (a, b) ∈ boundary n) :
    0 < a ∧ 0 < b ∧ a + b ≤ n + 1 := by
  rw [mem_boundary] at h
  rcases h with h | h | h <;> simp_all <;> omega

lemma boundary_assignment {n : ℕ} {lines : Finset Line} (hc : Covers n lines) :
    ∃ f : ℕ × ℕ → Line,
      ∀ p ∈ boundary n, f p ∈ lines ∧ OnLine (f p) p.1 p.2 := by
  classical
  choose f hfl hfp using fun p : ℕ × ℕ => hc p.1 p.2
  refine ⟨fun p => if hp : p ∈ boundary n then f p (boundary_triangle hp) else ∅, ?_⟩
  intro p hp
  simp only [hp, dite_true]
  exact ⟨hfl p (boundary_triangle hp), hfp p (boundary_triangle hp)⟩

def shell (n : ℕ) : Finset Line :=
  (Finset.Icc 5 (n + 1)).image (fun s : ℕ => affineLine 1 1 (-(s : ℝ)))

lemma shell_card {n : ℕ} : (shell n).card = n - 3 := by
  rw [shell, Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    have h := Set.ext_iff.mp hab ((0 : ℝ), (a : ℝ))
    norm_num [affineLine] at h
    have hc : (a : ℝ) = (b : ℝ) := by linarith
    exact_mod_cast hc

lemma shell_nonspecial {n : ℕ} {l : Line} (hl : l ∈ shell n) : ¬IsSpecial l := by
  simp only [shell, Finset.mem_image, Finset.mem_Icc] at hl
  rcases hl with ⟨s, hs, rfl⟩
  exact diagonal_affineLine_not_special (-(s : ℝ))

def specialBase : Finset Line :=
  {affineLine 1 (-1) 0, affineLine 1 2 (-5), affineLine 2 1 (-5)}

def specialLines (n : ℕ) : Finset Line := specialBase ∪ shell n

lemma specialBase_card : specialBase.card = 3 := by
  have h₁₂ : affineLine 1 (-1) 0 ≠ affineLine 1 2 (-5) := by
    intro h
    have hh := Set.ext_iff.mp h ((1 : ℝ), (1 : ℝ))
    norm_num [affineLine] at hh
  have h₁₃ : affineLine 1 (-1) 0 ≠ affineLine 2 1 (-5) := by
    intro h
    have hh := Set.ext_iff.mp h ((1 : ℝ), (1 : ℝ))
    norm_num [affineLine] at hh
  have h₂₃ : affineLine 1 2 (-5) ≠ affineLine 2 1 (-5) := by
    intro h
    have hh := Set.ext_iff.mp h ((1 : ℝ), (2 : ℝ))
    norm_num [affineLine] at hh
  simp [specialBase, h₁₂, h₁₃, h₂₃]

lemma specialBase_disjoint_shell (n : ℕ) : Disjoint specialBase (shell n) := by
  rw [Finset.disjoint_left]
  intro l hl hs
  simp only [specialBase, Finset.mem_insert, Finset.mem_singleton] at hl
  simp only [shell, Finset.mem_image, Finset.mem_Icc] at hs
  rcases hs with ⟨s, hss, rfl⟩
  rcases hl with hl | hl | hl
  · have h := Set.ext_iff.mp hl ((0 : ℝ), (0 : ℝ))
    norm_num [affineLine] at h
    omega
  · have h := Set.ext_iff.mp hl ((1 : ℝ), (2 : ℝ))
    norm_num [affineLine] at h
    have hc : (s : ℝ) = 3 := by linarith
    have hn : s = 3 := by exact_mod_cast hc
    omega
  · have h := Set.ext_iff.mp hl ((2 : ℝ), (1 : ℝ))
    norm_num [affineLine] at h
    have hc : (s : ℝ) = 3 := by linarith
    have hn : s = 3 := by exact_mod_cast hc
    omega

lemma specialLines_card {n : ℕ} (hn : n ≥ 3) : (specialLines n).card = n := by
  rw [specialLines, Finset.card_union_of_disjoint (specialBase_disjoint_shell n),
    specialBase_card, shell_card]
  omega

lemma specialLines_affine {n : ℕ} {l : Line} (hl : l ∈ specialLines n) : IsAffineLine l := by
  rw [specialLines, Finset.mem_union] at hl
  rcases hl with hl | hl
  · simp only [specialBase, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨1, -1, 0, by norm_num, rfl⟩
    · exact ⟨1, 2, -5, by norm_num, rfl⟩
    · exact ⟨2, 1, -5, by norm_num, rfl⟩
  · simp only [shell, Finset.mem_image, Finset.mem_Icc] at hl
    rcases hl with ⟨s, hs, rfl⟩
    exact ⟨1, 1, -(s : ℝ), by norm_num, rfl⟩

lemma specialLines_cover {n : ℕ} (hn : n ≥ 3) : Covers n (specialLines n) := by
  intro a b hab
  by_cases h11 : a = 1 ∧ b = 1
  · rcases h11 with ⟨rfl, rfl⟩
    exact ⟨affineLine 1 (-1) 0, by simp [specialLines, specialBase], by norm_num [OnLine, affineLine]⟩
  by_cases h22 : a = 2 ∧ b = 2
  · rcases h22 with ⟨rfl, rfl⟩
    exact ⟨affineLine 1 (-1) 0, by simp [specialLines, specialBase], by norm_num [OnLine, affineLine]⟩
  by_cases h12 : a = 1 ∧ b = 2
  · rcases h12 with ⟨rfl, rfl⟩
    exact ⟨affineLine 1 2 (-5), by simp [specialLines, specialBase], by norm_num [OnLine, affineLine]⟩
  by_cases h31 : a = 3 ∧ b = 1
  · rcases h31 with ⟨rfl, rfl⟩
    exact ⟨affineLine 1 2 (-5), by simp [specialLines, specialBase], by norm_num [OnLine, affineLine]⟩
  by_cases h13 : a = 1 ∧ b = 3
  · rcases h13 with ⟨rfl, rfl⟩
    exact ⟨affineLine 2 1 (-5), by simp [specialLines, specialBase], by norm_num [OnLine, affineLine]⟩
  by_cases h21 : a = 2 ∧ b = 1
  · rcases h21 with ⟨rfl, rfl⟩
    exact ⟨affineLine 2 1 (-5), by simp [specialLines, specialBase], by norm_num [OnLine, affineLine]⟩
  have hs : 5 ≤ a + b := by
    rcases hab with ⟨ha, hb, habn⟩
    omega
  refine ⟨affineLine 1 1 (-((a + b : ℕ) : ℝ)), ?_, ?_⟩
  · simp only [specialLines, Finset.mem_union]
    right
    simp only [shell, Finset.mem_image, Finset.mem_Icc]
    exact ⟨a + b, ⟨hs, hab.2.2⟩, rfl⟩
  · simp only [OnLine, affineLine, Set.mem_setOf_eq]
    norm_num

lemma specialBase_all_special {l : Line} (hl : l ∈ specialBase) : IsSpecial l := by
  simp only [specialBase, Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl
  · exact affineLine_special (by norm_num) (by norm_num) (by norm_num)
  · exact affineLine_special (by norm_num) (by norm_num) (by norm_num)
  · exact affineLine_special (by norm_num) (by norm_num) (by norm_num)

lemma specialLines_special_card {n : ℕ} :
    (by classical exact ((specialLines n).filter IsSpecial).card) = 3 := by
  classical
  apply (Finset.card_eq_three).mpr
  refine ⟨affineLine 1 (-1) 0, affineLine 1 2 (-5), affineLine 2 1 (-5), ?_, ?_, ?_, ?_⟩
  · intro h
    have hh := Set.ext_iff.mp h ((1 : ℝ), (1 : ℝ))
    norm_num [affineLine] at hh
  · intro h
    have hh := Set.ext_iff.mp h ((1 : ℝ), (1 : ℝ))
    norm_num [affineLine] at hh
  · intro h
    have hh := Set.ext_iff.mp h ((1 : ℝ), (2 : ℝ))
    norm_num [affineLine] at hh
  · apply Finset.ext
    intro l
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hl, hsp⟩
      rw [specialLines, Finset.mem_union] at hl
      rcases hl with hl | hl
      · simpa [specialBase] using hl
      · exact False.elim (shell_nonspecial hl hsp)
    · intro hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · exact ⟨by simp [specialLines, specialBase], affineLine_special (by norm_num) (by norm_num) (by norm_num)⟩
      · exact ⟨by simp [specialLines, specialBase], affineLine_special (by norm_num) (by norm_num) (by norm_num)⟩
      · exact ⟨by simp [specialLines, specialBase], affineLine_special (by norm_num) (by norm_num) (by norm_num)⟩

def shiftX (l : Line) : Line := {v : Point | (v.1 + 1, v.2) ∈ l}

def shiftY (l : Line) : Line := {v : Point | (v.1, v.2 + 1) ∈ l}

lemma shiftX_affine {l : Line} (hl : IsAffineLine l) : IsAffineLine (shiftX l) := by
  rcases hl with ⟨A, B, C, hnz, rfl⟩
  refine ⟨A, B, C + A, hnz, ?_⟩
  apply Set.ext
  intro v
  simp [shiftX, affineLine]
  ring_nf

lemma shiftY_affine {l : Line} (hl : IsAffineLine l) : IsAffineLine (shiftY l) := by
  rcases hl with ⟨A, B, C, hnz, rfl⟩
  refine ⟨A, B, C + B, hnz, ?_⟩
  apply Set.ext
  intro v
  simp [shiftY, affineLine]
  ring_nf

lemma shiftX_special {l : Line} : IsSpecial (shiftX l) ↔ IsSpecial l := by
  constructor
  · rintro ⟨A, B, C, hline, hA, hB, hAB⟩
    refine ⟨A, B, C - A, ?_, hA, hB, hAB⟩
    apply Set.ext
    intro v
    have hh := Set.ext_iff.mp hline (v.1 - 1, v.2)
    simp [shiftX, affineLine] at hh ⊢
    convert hh using 1 <;> ring
  · rintro ⟨A, B, C, hline, hA, hB, hAB⟩
    refine ⟨A, B, C + A, ?_, hA, hB, hAB⟩
    apply Set.ext
    intro v
    simp only [shiftX, affineLine, Set.mem_setOf_eq]
    rw [hline]
    change A * (v.1 + 1) + B * v.2 + C = 0 ↔ A * v.1 + B * v.2 + (C + A) = 0
    ring_nf

lemma shiftY_special {l : Line} : IsSpecial (shiftY l) ↔ IsSpecial l := by
  constructor
  · rintro ⟨A, B, C, hline, hA, hB, hAB⟩
    refine ⟨A, B, C - B, ?_, hA, hB, hAB⟩
    apply Set.ext
    intro v
    have hh := Set.ext_iff.mp hline (v.1, v.2 - 1)
    simp [shiftY, affineLine] at hh ⊢
    convert hh using 1 <;> ring
  · rintro ⟨A, B, C, hline, hA, hB, hAB⟩
    refine ⟨A, B, C + B, ?_, hA, hB, hAB⟩
    apply Set.ext
    intro v
    simp only [shiftY, affineLine, Set.mem_setOf_eq]
    rw [hline]
    change A * v.1 + B * (v.2 + 1) + C = 0 ↔ A * v.1 + B * v.2 + (C + B) = 0
    ring_nf

lemma shiftX_injective : Function.Injective shiftX := by
  intro l m h
  apply Set.ext
  intro v
  have hh := Set.ext_iff.mp h (v.1 - 1, v.2)
  simpa [shiftX] using hh

lemma shiftY_injective : Function.Injective shiftY := by
  intro l m h
  apply Set.ext
  intro v
  have hh := Set.ext_iff.mp h (v.1, v.2 - 1)
  simpa [shiftY] using hh

lemma shiftX_cover {n : ℕ} (hn : n ≥ 4) {lines : Finset Line} (hc : Covers n lines) :
    Covers (n - 1) ((lines.erase vertical).image shiftX) := by
  intro a b hab
  rcases hab with ⟨ha, hb, hs⟩
  have habn : 0 < a + 1 ∧ 0 < b ∧ (a + 1) + b ≤ n + 1 := by omega
  obtain ⟨l, hl, hon⟩ := hc (a + 1) b habn
  refine ⟨shiftX l, Finset.mem_image.mpr ⟨l, Finset.mem_erase.mpr ⟨?_, hl⟩, rfl⟩, ?_⟩
  · intro heq
    subst l
    simp only [OnLine, vertical, affineLine, Set.mem_setOf_eq] at hon
    norm_num at hon
    have hcasteq : ((a : ℝ) + 1 = 1) := by linarith
    have hnateq : a + 1 = 1 := by exact_mod_cast hcasteq
    omega
  · simpa [OnLine, shiftX] using hon

lemma shiftY_cover {n : ℕ} (hn : n ≥ 4) {lines : Finset Line} (hc : Covers n lines) :
    Covers (n - 1) ((lines.erase horizontal).image shiftY) := by
  intro a b hab
  rcases hab with ⟨ha, hb, hs⟩
  have habn : 0 < a ∧ 0 < b + 1 ∧ a + (b + 1) ≤ n + 1 := by omega
  obtain ⟨l, hl, hon⟩ := hc a (b + 1) habn
  refine ⟨shiftY l, Finset.mem_image.mpr ⟨l, Finset.mem_erase.mpr ⟨?_, hl⟩, rfl⟩, ?_⟩
  · intro heq
    subst l
    simp only [OnLine, horizontal, affineLine, Set.mem_setOf_eq] at hon
    norm_num at hon
    have hcasteq : ((b : ℝ) + 1 = 1) := by linarith
    have hnateq : b + 1 = 1 := by exact_mod_cast hcasteq
    omega
  · simpa [OnLine, shiftY] using hon

lemma diagonal_cover {n : ℕ} (hn : n ≥ 4) {lines : Finset Line} (hc : Covers n lines) :
    Covers (n - 1) (lines.erase (diagonal n)) := by
  intro a b hab
  rcases hab with ⟨ha, hb, hs⟩
  have habn : 0 < a ∧ 0 < b ∧ a + b ≤ n + 1 := by omega
  obtain ⟨l, hl, hon⟩ := hc a b habn
  refine ⟨l, Finset.mem_erase.mpr ⟨?_, hl⟩, hon⟩
  intro heq
  subst l
  simp only [OnLine, diagonal, affineLine, Set.mem_setOf_eq] at hon
  norm_num at hon
  have hcasteq : ((a : ℝ) + (b : ℝ) = (n : ℝ) + 1) := by nlinarith
  have hnateq : a + b = n + 1 := by exact_mod_cast hcasteq
  omega

lemma shiftX_count {lines : Finset Line} :
    (by classical exact (((lines.erase vertical).image shiftX).filter IsSpecial).card) =
      (by classical exact (lines.filter IsSpecial).card) := by
  classical
  rw [Finset.filter_image]
  have heq :
      (lines.erase vertical).filter (fun l => IsSpecial (shiftX l)) =
        lines.filter IsSpecial := by
    apply Finset.ext
    intro l
    simp only [Finset.mem_filter, Finset.mem_erase]
    rw [shiftX_special]
    constructor
    · rintro ⟨⟨hlv, hl⟩, hsp⟩
      exact ⟨hl, hsp⟩
    · rintro ⟨hl, hsp⟩
      exact ⟨⟨by intro e; subst l; exact vertical_not_special hsp, hl⟩, hsp⟩
  rw [heq, Finset.card_image_iff.mpr]
  intro a ha b hb hab
  exact shiftX_injective hab

lemma shiftY_count {lines : Finset Line} :
    (by classical exact (((lines.erase horizontal).image shiftY).filter IsSpecial).card) =
      (by classical exact (lines.filter IsSpecial).card) := by
  classical
  rw [Finset.filter_image]
  have heq :
      (lines.erase horizontal).filter (fun l => IsSpecial (shiftY l)) =
        lines.filter IsSpecial := by
    apply Finset.ext
    intro l
    simp only [Finset.mem_filter, Finset.mem_erase]
    rw [shiftY_special]
    constructor
    · rintro ⟨⟨hlv, hl⟩, hsp⟩
      exact ⟨hl, hsp⟩
    · rintro ⟨hl, hsp⟩
      exact ⟨⟨by intro e; subst l; exact horizontal_not_special hsp, hl⟩, hsp⟩
  rw [heq, Finset.card_image_iff.mpr]
  intro a ha b hb hab
  exact shiftY_injective hab

lemma diagonal_count {n : ℕ} {lines : Finset Line} :
    (by classical exact ((lines.erase (diagonal n)).filter IsSpecial).card) =
      (by classical exact (lines.filter IsSpecial).card) := by
  classical
  rw [Finset.filter_erase, Finset.erase_eq_self.mpr]
  simp only [Finset.mem_filter, not_and_or]
  exact Or.inr (diagonal_not_special n)

def sidePoint (n : ℕ) (i : Fin 3) (t : Fin n) : ℕ × ℕ :=
  match i with
  | 0 => (1, t.1 + 1)
  | 1 => (t.1 + 1, 1)
  | 2 => (t.1 + 1, n - t.1)

lemma sidePoint_triangle {n : ℕ} (hn : 0 < n) (i : Fin 3) (t : Fin n) :
    0 < (sidePoint n i t).1 ∧ 0 < (sidePoint n i t).2 ∧
      (sidePoint n i t).1 + (sidePoint n i t).2 ≤ n + 1 := by
  fin_cases i <;> simp [sidePoint] <;> omega

lemma chosen_side_line {n : ℕ} (hn : 0 < n) (i : Fin 3) {lines : Finset Line}
    (hcover : Covers n lines) (t : Fin n) : ∃ l ∈ lines,
      OnLine l (sidePoint n i t).1 (sidePoint n i t).2 := by
  exact hcover _ _ (sidePoint_triangle hn i t)

noncomputable def sideAssignment {n : ℕ} (hn : 0 < n) (i : Fin 3)
    (lines : Finset Line) (hcover : Covers n lines) (t : Fin n) : Line :=
  Classical.choose (chosen_side_line hn i hcover t)

lemma sideAssignment_mem {n : ℕ} (hn : 0 < n) (i : Fin 3)
    (lines : Finset Line) (hcover : Covers n lines) (t : Fin n) :
    sideAssignment hn i lines hcover t ∈ lines :=
  (Classical.choose_spec (chosen_side_line hn i hcover t)).1

lemma sideAssignment_on {n : ℕ} (hn : 0 < n) (i : Fin 3)
    (lines : Finset Line) (hcover : Covers n lines) (t : Fin n) :
    OnLine (sideAssignment hn i lines hcover t)
      (sidePoint n i t).1 (sidePoint n i t).2 :=
  (Classical.choose_spec (chosen_side_line hn i hcover t)).2

lemma sideAssignment_injective {n : ℕ} (hn : 0 < n) (i : Fin 3)
    {lines : Finset Line} (haff : ∀ l ∈ lines, IsAffineLine l)
    (hcover : Covers n lines)
    (hns : vertical ∉ lines ∧ horizontal ∉ lines ∧ diagonal n ∉ lines) :
    Function.Injective (sideAssignment hn i lines hcover) := by
  intro p q heq
  by_contra hpq
  have hpmem := sideAssignment_mem hn i lines hcover p
  have hqmem := sideAssignment_mem hn i lines hcover q
  have hpon := sideAssignment_on hn i lines hcover p
  have hqon := sideAssignment_on hn i lines hcover q
  fin_cases i
  · simp only [sidePoint] at hpon hqon
    have hqon' : OnLine (sideAssignment hn 0 lines hcover p) 1 (q.1 + 1) := by
      exact heq ▸ hqon
    have hcoord : p.1 + 1 ≠ q.1 + 1 := by
      intro e
      apply hpq
      apply Fin.ext
      omega
    have hline := vertical_eq_of_two (haff _ hpmem) hcoord hpon hqon'
    exact hns.1 (hline ▸ hpmem)
  · simp only [sidePoint] at hpon hqon
    have hqon' : OnLine (sideAssignment hn 1 lines hcover p) (q.1 + 1) 1 := by
      exact heq ▸ hqon
    have hcoord : p.1 + 1 ≠ q.1 + 1 := by
      intro e
      apply hpq
      apply Fin.ext
      omega
    have hline := horizontal_eq_of_two (haff _ hpmem) hcoord hpon hqon'
    exact hns.2.1 (hline ▸ hpmem)
  · simp only [sidePoint] at hpon hqon
    have hqon' : OnLine (sideAssignment hn 2 lines hcover p) (q.1 + 1) (n - q.1) := by
      exact heq ▸ hqon
    have hcoord : p.1 + 1 ≠ q.1 + 1 := by
      intro e
      apply hpq
      apply Fin.ext
      omega
    have hpform : n - p.1 = n + 1 - (p.1 + 1) := by omega
    have hqform : n - q.1 = n + 1 - (q.1 + 1) := by omega
    rw [hpform] at hpon
    rw [hqform] at hqon'
    have hline := diagonal_eq_of_two (haff _ hpmem) hcoord hpon hqon'
      (by omega) (by omega)
    exact hns.2.2 (hline ▸ hpmem)

lemma no_side_cover_impossible {n : ℕ} (hn : n ≥ 4) {lines : Finset Line}
    (hcard : lines.card = n) (haff : ∀ l ∈ lines, IsAffineLine l)
    (hcover : Covers n lines)
    (hns : vertical ∉ lines ∧ horizontal ∉ lines ∧ diagonal n ∉ lines) : False := by
  let f : Fin 3 × Fin n → Line := fun it => sideAssignment (by omega) it.1 lines hcover it.2
  have hfmem : ∀ it, f it ∈ lines := by
    intro it
    exact sideAssignment_mem (by omega) it.1 lines hcover it.2
  have hsideinj : ∀ i : Fin 3, Function.Injective (fun t : Fin n => f (i, t)) := by
    intro i
    exact sideAssignment_injective (by omega) i haff hcover hns
  have hbij : ∀ i : Fin 3,
      Function.Bijective (fun t : Fin n => (⟨f (i, t), hfmem (i, t)⟩ : lines)) := by
    intro i
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · intro p q heq
      apply hsideinj i
      exact congrArg Subtype.val heq
    · simp [hcard]
  have hsurj : ∀ i : Fin 3,
      Function.Surjective (fun t : Fin n => (⟨f (i, t), hfmem (i, t)⟩ : lines)) :=
    fun i => (hbij i).2
  have hvertices : ∀ l ∈ lines,
      OnLine l 1 1 ∨ OnLine l 1 n ∨ OnLine l n 1 := by
    intro l hl
    obtain ⟨p, hp⟩ := hsurj 0 ⟨l, hl⟩
    obtain ⟨q, hq⟩ := hsurj 1 ⟨l, hl⟩
    obtain ⟨r, hr⟩ := hsurj 2 ⟨l, hl⟩
    have hpv : f (0, p) = l := congrArg Subtype.val hp
    have hqv : f (1, q) = l := congrArg Subtype.val hq
    have hrv : f (2, r) = l := congrArg Subtype.val hr
    have hpon := sideAssignment_on (by omega) 0 lines hcover p
    have hqon := sideAssignment_on (by omega) 1 lines hcover q
    have hron := sideAssignment_on (by omega) 2 lines hcover r
    simp only [sidePoint, f] at hpon hqon hron
    change sideAssignment (by omega) 0 lines hcover p = l at hpv
    change sideAssignment (by omega) 1 lines hcover q = l at hqv
    change sideAssignment (by omega) 2 lines hcover r = l at hrv
    rw [hpv] at hpon
    rw [hqv] at hqon
    rw [hrv] at hron
    have hreal := vertex_of_three_side_points (haff l hl)
      (p := (p.1 : ℝ)) (q := (q.1 : ℝ)) (r := (r.1 : ℝ))
      (n := n - 1)
      (by positivity) (by
        have hp_le : p.1 ≤ n - 1 := by omega
        exact_mod_cast hp_le)
      (by positivity) (by
        have hq_le : q.1 ≤ n - 1 := by omega
        exact_mod_cast hq_le)
      (by positivity) (by
        have hr_le : r.1 ≤ n - 1 := by omega
        exact_mod_cast hr_le)
      (by simpa [OnLine] using hpon) (by simpa [OnLine] using hqon)
      (by
        have hncast : (((n - 1 : ℕ) : ℝ) - (r.1 : ℝ) + 1) = ((n - r.1 : ℕ) : ℝ) := by
          have hrle : r.1 ≤ n := by omega
          rw [Nat.cast_sub hrle]
          push_cast
          have hnpos : 0 < n := by omega
          have hnsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ n)]
            norm_num
          rw [hnsub]
          ring
        simpa [OnLine, hncast] using hron)
    simp only [OnLine]
    have hnreal : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
      norm_num
      exact_mod_cast (show n - 1 + 1 = n by omega)
    rw [hnreal] at hreal
    simpa only [Nat.cast_one] using hreal
  -- Since each side assignment is bijective, every vertex belongs to a unique line.
  have hle : lines.card ≤ 3 := by
    classical
    let vertexType : Line → Fin 3 := fun l =>
      if OnLine l 1 1 then 0 else if OnLine l 1 n then 1 else 2
    apply Finset.card_le_card_of_injOn vertexType (fun l hl => Finset.mem_univ _)
    intro l hl m hm heq
    by_cases hl0 : OnLine l 1 1
    · have hm0 : OnLine m 1 1 := by
        by_contra hm0
        by_cases hm1 : OnLine m 1 n
        · simp [vertexType, hl0, hm0, hm1] at heq
        · simp [vertexType, hl0, hm0, hm1] at heq
      obtain ⟨tl, htl⟩ := hsurj 0 ⟨l, hl⟩
      obtain ⟨tm, htm⟩ := hsurj 0 ⟨m, hm⟩
      have htlv : f (0, tl) = l := congrArg Subtype.val htl
      have htmv : f (0, tm) = m := congrArg Subtype.val htm
      have htlon := sideAssignment_on (by omega) 0 lines hcover tl
      have htmon := sideAssignment_on (by omega) 0 lines hcover tm
      simp only [sidePoint] at htlon htmon
      change sideAssignment (by omega) 0 lines hcover tl = l at htlv
      change sideAssignment (by omega) 0 lines hcover tm = m at htmv
      rw [htlv] at htlon
      rw [htmv] at htmon
      have htl0 : tl.1 = 0 := by
        by_contra hne
        have hcoord : tl.1 + 1 ≠ 1 := by omega
        have hline := vertical_eq_of_two (haff l hl) hcoord htlon hl0
        exact hns.1 (hline ▸ hl)
      have htm0 : tm.1 = 0 := by
        by_contra hne
        have hcoord : tm.1 + 1 ≠ 1 := by omega
        have hline := vertical_eq_of_two (haff m hm) hcoord htmon hm0
        exact hns.1 (hline ▸ hm)
      have hteq : tl = tm := by apply Fin.ext; omega
      exact htlv.symm.trans ((congrArg (fun t => f (0, t)) hteq).trans htmv)
    · by_cases hl1 : OnLine l 1 n
      · have hm0 : ¬OnLine m 1 1 := by
          intro hm0
          simp [vertexType, hl0, hl1, hm0] at heq
        have hm1 : OnLine m 1 n := by
          by_contra hm1
          simp [vertexType, hl0, hl1, hm0, hm1] at heq
        obtain ⟨tl, htl⟩ := hsurj 0 ⟨l, hl⟩
        obtain ⟨tm, htm⟩ := hsurj 0 ⟨m, hm⟩
        have htlv : f (0, tl) = l := congrArg Subtype.val htl
        have htmv : f (0, tm) = m := congrArg Subtype.val htm
        have htlon := sideAssignment_on (by omega) 0 lines hcover tl
        have htmon := sideAssignment_on (by omega) 0 lines hcover tm
        simp only [sidePoint] at htlon htmon
        change sideAssignment (by omega) 0 lines hcover tl = l at htlv
        change sideAssignment (by omega) 0 lines hcover tm = m at htmv
        rw [htlv] at htlon
        rw [htmv] at htmon
        have htln : tl.1 + 1 = n := by
          by_contra hne
          have hline := vertical_eq_of_two (haff l hl) hne htlon hl1
          exact hns.1 (hline ▸ hl)
        have htmn : tm.1 + 1 = n := by
          by_contra hne
          have hline := vertical_eq_of_two (haff m hm) hne htmon hm1
          exact hns.1 (hline ▸ hm)
        have hteq : tl = tm := by apply Fin.ext; omega
        exact htlv.symm.trans ((congrArg (fun t => f (0, t)) hteq).trans htmv)
      · have hl2 : OnLine l n 1 := by
          rcases hvertices l hl with h | h | h
          · exact False.elim (hl0 h)
          · exact False.elim (hl1 h)
          · exact h
        have hm0 : ¬OnLine m 1 1 := by
          intro hm0
          simp [vertexType, hl0, hl1, hm0] at heq
        have hm1 : ¬OnLine m 1 n := by
          intro hm1
          simp [vertexType, hl0, hl1, hm0, hm1] at heq
        have hm2 : OnLine m n 1 := by
          rcases hvertices m hm with h | h | h
          · exact False.elim (hm0 h)
          · exact False.elim (hm1 h)
          · exact h
        obtain ⟨tl, htl⟩ := hsurj 1 ⟨l, hl⟩
        obtain ⟨tm, htm⟩ := hsurj 1 ⟨m, hm⟩
        have htlv : f (1, tl) = l := congrArg Subtype.val htl
        have htmv : f (1, tm) = m := congrArg Subtype.val htm
        have htlon := sideAssignment_on (by omega) 1 lines hcover tl
        have htmon := sideAssignment_on (by omega) 1 lines hcover tm
        simp only [sidePoint] at htlon htmon
        change sideAssignment (by omega) 1 lines hcover tl = l at htlv
        change sideAssignment (by omega) 1 lines hcover tm = m at htmv
        rw [htlv] at htlon
        rw [htmv] at htmon
        have htln : tl.1 + 1 = n := by
          by_contra hne
          have hline := horizontal_eq_of_two (haff l hl) hne htlon hl2
          exact hns.2.1 (hline ▸ hl)
        have htmn : tm.1 + 1 = n := by
          by_contra hne
          have hline := horizontal_eq_of_two (haff m hm) hne htmon hm2
          exact hns.2.1 (hline ▸ hm)
        have hteq : tl = tm := by apply Fin.ext; omega
        exact htlv.symm.trans ((congrArg (fun t => f (1, t)) hteq).trans htmv)
  omega

set_option maxHeartbeats 100000000 in
lemma special_count_classification : ∀ n : ℕ, n ≥ 3 → ∀ lines : Finset Line,
    lines.card = n → (∀ l ∈ lines, IsAffineLine l) → Covers n lines →
    (by classical exact (lines.filter IsSpecial).card) = 0 ∨
    (by classical exact (lines.filter IsSpecial).card) = 1 ∨
    (by classical exact (lines.filter IsSpecial).card) = 3 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro lines hcard haff hcover
    by_cases hn3 : n = 3
    · have hcard3 : lines.card = 3 := by omega
      have hle : (by classical exact (lines.filter IsSpecial).card) ≤ 3 := by
        classical
        calc
          (lines.filter IsSpecial).card ≤ lines.card := Finset.card_filter_le _ _
          _ = 3 := hcard3
      by_contra H
      have htwo : (by classical exact (lines.filter IsSpecial).card) = 2 := by omega
      classical
      let ordinary := lines.filter (fun l => ¬IsSpecial l)
      have hpartition := Finset.card_filter_add_card_filter_not (s := lines) IsSpecial
      have hordinary : ordinary.card = 1 := by
        dsimp [ordinary]
        omega
      obtain ⟨L, hL⟩ := Finset.card_eq_one.mp hordinary
      have hLmem : L ∈ lines := by
        have : L ∈ ordinary := by simp [hL]
        exact (Finset.mem_filter.mp this).1
      have hLns : ¬IsSpecial L := by
        have : L ∈ ordinary := by simp [hL]
        exact (Finset.mem_filter.mp this).2
      have hLaff := haff L hLmem
      have hunique : ∀ l ∈ lines, ¬IsSpecial l → l = L := by
        intro l hl hlns
        have : l ∈ ordinary := Finset.mem_filter.mpr ⟨hl, hlns⟩
        simpa [hL] using this
      have hc11 := hcover 1 1 (by norm_num; omega)
      have hc12 := hcover 1 2 (by norm_num; omega)
      have hc13 := hcover 1 3 (by norm_num; omega)
      have hc21 := hcover 2 1 (by norm_num; omega)
      have hc22 := hcover 2 2 (by norm_num; omega)
      have hc31 := hcover 3 1 (by norm_num; omega)
      rcases hc11 with ⟨l11, hl11, h11⟩
      rcases hc12 with ⟨l12, hl12, h12⟩
      rcases hc13 with ⟨l13, hl13, h13⟩
      rcases hc21 with ⟨l21, hl21, h21⟩
      rcases hc22 with ⟨l22, hl22, h22⟩
      rcases hc31 with ⟨l31, hl31, h31⟩
      classical
      let S : Finset Line := lines.filter IsSpecial
      have hS : S.card = 2 := by simpa [S] using htwo
      obtain ⟨U, V, hUV, hSUV⟩ := Finset.card_eq_two.mp hS
      have hUmemS : U ∈ S := by simp [hSUV]
      have hVmemS : V ∈ S := by simp [hSUV]
      have hUmem : U ∈ lines := (Finset.mem_filter.mp hUmemS).1
      have hVmem : V ∈ lines := (Finset.mem_filter.mp hVmemS).1
      have hUsp : IsSpecial U := (Finset.mem_filter.mp hUmemS).2
      have hVsp : IsSpecial V := (Finset.mem_filter.mp hVmemS).2
      have hlines : lines = {L, U, V} := by
        apply Finset.ext
        intro l
        constructor
        · intro hl
          by_cases hsp : IsSpecial l
          · have : l ∈ S := Finset.mem_filter.mpr ⟨hl, hsp⟩
            rw [hSUV] at this
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            aesop
          · have : l = L := hunique l hl hsp
            simp [this]
        · intro hl
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl | rfl
          · exact hLmem
          · exact hUmem
          · exact hVmem
      have hUL : U ≠ L := by
        intro h; subst U; exact hLns hUsp
      have hVL : V ≠ L := by
        intro h; subst V; exact hLns hVsp
      have hLU : L ≠ U := Ne.symm hUL
      have hLV : L ≠ V := Ne.symm hVL
      have hVU : V ≠ U := Ne.symm hUV
      rw [hlines] at hl11 hl12 hl13 hl21 hl22 hl31
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl11 hl12 hl13 hl21 hl22 hl31
      have hcoverL : ∀ a b : ℕ, (a, b) = (1, 1) ∨ (a, b) = (1, 2) ∨
          (a, b) = (1, 3) ∨ (a, b) = (2, 1) ∨ (a, b) = (2, 2) ∨
          (a, b) = (3, 1) → OnLine L a b ∨ OnLine U a b ∨ OnLine V a b := by
        intro a b hp
        rcases hp with hp | hp | hp | hp | hp | hp
        · have ha : a = 1 := congrArg Prod.fst hp
          have hb : b = 1 := congrArg Prod.snd hp
          subst a; subst b
          rcases hl11 with rfl | rfl | rfl <;> aesop
        · have ha : a = 1 := congrArg Prod.fst hp
          have hb : b = 2 := congrArg Prod.snd hp
          subst a; subst b
          rcases hl12 with rfl | rfl | rfl <;> aesop
        · have ha : a = 1 := congrArg Prod.fst hp
          have hb : b = 3 := congrArg Prod.snd hp
          subst a; subst b
          rcases hl13 with rfl | rfl | rfl <;> aesop
        · have ha : a = 2 := congrArg Prod.fst hp
          have hb : b = 1 := congrArg Prod.snd hp
          subst a; subst b
          rcases hl21 with rfl | rfl | rfl <;> aesop
        · have ha : a = 2 := congrArg Prod.fst hp
          have hb : b = 2 := congrArg Prod.snd hp
          subst a; subst b
          rcases hl22 with rfl | rfl | rfl <;> aesop
        · have ha : a = 3 := congrArg Prod.fst hp
          have hb : b = 1 := congrArg Prod.snd hp
          subst a; subst b
          rcases hl31 with rfl | rfl | rfl <;> aesop
      have hUthree : ¬((OnLine U 1 1 ∧ OnLine U 1 2 ∧ OnLine U 1 3) ∨
          (OnLine U 1 1 ∧ OnLine U 2 1 ∧ OnLine U 3 1) ∨
          (OnLine U 1 3 ∧ OnLine U 2 2 ∧ OnLine U 3 1)) := by
        rintro (h | h | h)
        · have hline := vertical_eq_of_two (haff U hUmem) (by norm_num) h.1 h.2.1
          rw [hline] at hUsp
          exact vertical_not_special hUsp
        · have hline := horizontal_eq_of_two (haff U hUmem) (by norm_num) h.1 h.2.1
          rw [hline] at hUsp
          exact horizontal_not_special hUsp
        · have hline := diagonal_eq_of_two (n := 3) (haff U hUmem) (by norm_num)
            h.1 h.2.1 (by omega) (by omega)
          rw [hline] at hUsp
          exact diagonal_not_special 3 hUsp
      have hVthree : ¬((OnLine V 1 1 ∧ OnLine V 1 2 ∧ OnLine V 1 3) ∨
          (OnLine V 1 1 ∧ OnLine V 2 1 ∧ OnLine V 3 1) ∨
          (OnLine V 1 3 ∧ OnLine V 2 2 ∧ OnLine V 3 1)) := by
        rintro (h | h | h)
        · have hline := vertical_eq_of_two (haff V hVmem) (by norm_num) h.1 h.2.1
          rw [hline] at hVsp
          exact vertical_not_special hVsp
        · have hline := horizontal_eq_of_two (haff V hVmem) (by norm_num) h.1 h.2.1
          rw [hline] at hVsp
          exact horizontal_not_special hVsp
        · have hline := diagonal_eq_of_two (n := 3) (haff V hVmem) (by norm_num)
            h.1 h.2.1 (by omega) (by omega)
          rw [hline] at hVsp
          exact diagonal_not_special 3 hVsp
      have hLcol : ∀ {a b c d : ℕ}, OnLine L a b → OnLine L c d →
          a = c ∨ b = d ∨ a + b = c + d :=
        fun h₁ h₂ => nonspecial_pair hLaff hLns h₁ h₂
      rcases hcoverL 1 1 (by aesop) with hL11 | hU11 | hV11 <;>
      rcases hcoverL 1 2 (by aesop) with hL12 | hU12 | hV12 <;>
      rcases hcoverL 1 3 (by aesop) with hL13 | hU13 | hV13 <;>
      rcases hcoverL 2 1 (by aesop) with hL21 | hU21 | hV21 <;>
      rcases hcoverL 2 2 (by aesop) with hL22 | hU22 | hV22 <;>
      rcases hcoverL 3 1 (by aesop) with hL31 | hU31 | hV31
      all_goals first
        | (have := special_same_x_false hUsp (by norm_num) hU11 hU12; contradiction)
        | (have := special_same_x_false hUsp (by norm_num) hU11 hU13; contradiction)
        | (have := special_same_x_false hUsp (by norm_num) hU12 hU13; contradiction)
        | (have := special_same_x_false hVsp (by norm_num) hV11 hV12; contradiction)
        | (have := special_same_x_false hVsp (by norm_num) hV11 hV13; contradiction)
        | (have := special_same_x_false hVsp (by norm_num) hV12 hV13; contradiction)
        | (have := special_same_y_false hUsp (by norm_num) hU11 hU21; contradiction)
        | (have := special_same_y_false hUsp (by norm_num) hU11 hU31; contradiction)
        | (have := special_same_y_false hUsp (by norm_num) hU21 hU31; contradiction)
        | (have := special_same_y_false hUsp (by norm_num) hU12 hU22; contradiction)
        | (have := special_same_y_false hVsp (by norm_num) hV11 hV21; contradiction)
        | (have := special_same_y_false hVsp (by norm_num) hV11 hV31; contradiction)
        | (have := special_same_y_false hVsp (by norm_num) hV21 hV31; contradiction)
        | (have := special_same_y_false hVsp (by norm_num) hV12 hV22; contradiction)
        | (have := special_same_sum_false hUsp (by norm_num) (by norm_num) hU12 hU21; contradiction)
        | (have := special_same_sum_false hUsp (by norm_num) (by norm_num) hU13 hU22; contradiction)
        | (have := special_same_sum_false hUsp (by norm_num) (by norm_num) hU13 hU31; contradiction)
        | (have := special_same_sum_false hUsp (by norm_num) (by norm_num) hU22 hU31; contradiction)
        | (have := special_same_sum_false hVsp (by norm_num) (by norm_num) hV12 hV21; contradiction)
        | (have := special_same_sum_false hVsp (by norm_num) (by norm_num) hV13 hV22; contradiction)
        | (have := special_same_sum_false hVsp (by norm_num) (by norm_num) hV13 hV31; contradiction)
        | (have := special_same_sum_false hVsp (by norm_num) (by norm_num) hV22 hV31; contradiction)
        | (have := special_same_x_false hUsp (by norm_num) hU21 hU22; contradiction)
        | (have := special_same_x_false hVsp (by norm_num) hV21 hV22; contradiction)
        | (have hp := hLcol hL11 hL22; norm_num at hp)
        | (have hp := hLcol hL12 hL31; norm_num at hp)
        | (have hp := hLcol hL13 hL21; norm_num at hp)
    · have hn4 : n ≥ 4 := by omega
      have hside : vertical ∈ lines ∨ horizontal ∈ lines ∨ diagonal n ∈ lines := by
        by_contra hnot
        push Not at hnot
        exact no_side_cover_impossible hn4 hcard haff hcover hnot
      rcases hside with hv | hh | hd
      · let reduced := (lines.erase vertical).image shiftX
        have hredcard : reduced.card = n - 1 := by
          dsimp [reduced]
          rw [Finset.card_image_iff.mpr]
          · rw [Finset.card_erase_of_mem hv, hcard]
          · intro a ha b hb hab
            exact shiftX_injective hab
        have hredaff : ∀ l ∈ reduced, IsAffineLine l := by
          intro l hl
          rcases Finset.mem_image.mp hl with ⟨m, hm, rfl⟩
          exact shiftX_affine (haff m (Finset.mem_of_mem_erase hm))
        have hredcover : Covers (n - 1) reduced := shiftX_cover hn4 hcover
        have hres := ih (n - 1) (by omega) (by omega) reduced hredcard hredaff hredcover
        simpa [reduced, shiftX_count] using hres
      · let reduced := (lines.erase horizontal).image shiftY
        have hredcard : reduced.card = n - 1 := by
          dsimp [reduced]
          rw [Finset.card_image_iff.mpr]
          · rw [Finset.card_erase_of_mem hh, hcard]
          · intro a ha b hb hab
            exact shiftY_injective hab
        have hredaff : ∀ l ∈ reduced, IsAffineLine l := by
          intro l hl
          rcases Finset.mem_image.mp hl with ⟨m, hm, rfl⟩
          exact shiftY_affine (haff m (Finset.mem_of_mem_erase hm))
        have hredcover : Covers (n - 1) reduced := shiftY_cover hn4 hcover
        have hres := ih (n - 1) (by omega) (by omega) reduced hredcard hredaff hredcover
        simpa [reduced, shiftY_count] using hres
      · let reduced := lines.erase (diagonal n)
        have hredcard : reduced.card = n - 1 := by
          dsimp [reduced]
          rw [Finset.card_erase_of_mem hd, hcard]
        have hredaff : ∀ l ∈ reduced, IsAffineLine l := by
          intro l hl
          exact haff l (Finset.mem_of_mem_erase hl)
        have hredcover : Covers (n - 1) reduced := diagonal_cover hn4 hcover
        have hres := ih (n - 1) (by omega) (by omega) reduced hredcard hredaff hredcover
        simpa [reduced, diagonal_count] using hres

def verticalFamily (n : ℕ) : Finset Line :=
  (Finset.Icc 1 n).image (fun s : ℕ => affineLine 1 0 (-(s : ℝ)))

lemma verticalFamily_card {n : ℕ} : (verticalFamily n).card = n := by
  rw [verticalFamily, Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    have h := Set.ext_iff.mp hab ((a : ℝ), (0 : ℝ))
    norm_num [affineLine] at h
    have hc : (a : ℝ) = (b : ℝ) := by linarith
    exact_mod_cast hc

lemma verticalFamily_affine {n : ℕ} {l : Line} (hl : l ∈ verticalFamily n) : IsAffineLine l := by
  simp only [verticalFamily, Finset.mem_image, Finset.mem_Icc] at hl
  rcases hl with ⟨s, hs, rfl⟩
  exact ⟨1, 0, -(s : ℝ), by norm_num, rfl⟩

lemma verticalFamily_cover {n : ℕ} : Covers n (verticalFamily n) := by
  intro a b hab
  refine ⟨affineLine 1 0 (-(a : ℝ)), ?_, ?_⟩
  · simp only [verticalFamily, Finset.mem_image, Finset.mem_Icc]
    exact ⟨a, ⟨by omega, by omega⟩, rfl⟩
  · norm_num [OnLine, affineLine]

lemma verticalFamily_special_card {n : ℕ} :
    (by classical exact ((verticalFamily n).filter IsSpecial).card) = 0 := by
  classical
  rw [Finset.card_filter_eq_zero_iff]
  intro l hl
  simp only [verticalFamily, Finset.mem_image, Finset.mem_Icc] at hl
  rcases hl with ⟨s, hs, rfl⟩
  rintro ⟨A, B, C, hline, hA, hB, hAB⟩
  have hp := Set.ext_iff.mp hline ((-C / A : ℝ), (0 : ℝ))
  have hp2 := Set.ext_iff.mp hline ((-C / A : ℝ), (1 : ℝ))
  simp only [affineLine, Set.mem_setOf_eq] at hp hp2
  have hzero : A * (-C / A) + C = 0 := by
    rw [div_eq_mul_inv]
    calc
      A * (-C * A⁻¹) + C = -(C * (A * A⁻¹)) + C := by ring
      _ = 0 := by rw [mul_inv_cancel₀ hA]; ring
  have hx := hp.mpr (by nlinarith [hzero])
  have hx2 := hp2.mp (by nlinarith [hx])
  have hBzero : B = 0 := by nlinarith [hzero, hx2]
  exact hB hBzero

def oblique (n : ℕ) : Line := affineLine 1 (-1) (-((n - 1 : ℕ) : ℝ))

def oneFamily (n : ℕ) : Finset Line := insert (oblique n) (verticalFamily (n - 1))

lemma oblique_not_verticalFamily {n : ℕ} (hn : n ≥ 2) :
    oblique n ∉ verticalFamily (n - 1) := by
  intro h
  simp only [verticalFamily, Finset.mem_image, Finset.mem_Icc] at h
  rcases h with ⟨s, hs, heq⟩
  have hp := Set.ext_iff.mp heq (((n : ℕ) : ℝ), (1 : ℝ))
  simp only [oblique, affineLine, Set.mem_setOf_eq] at hp
  have hnsub : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hnsub] at hp
  have hslt : s < n := by omega
  have hcast : (s : ℝ) < (n : ℝ) := by exact_mod_cast hslt
  have hps : (s : ℝ) = (n : ℝ) := by
    have hright : 1 * (n : ℝ) + (-1) * 1 + (-((n : ℝ) - 1)) = 0 := by ring
    have hleft := hp.mpr hright
    norm_num at hleft
    linarith
  exact (ne_of_lt hcast) hps

lemma oneFamily_card {n : ℕ} (hn : n ≥ 3) : (oneFamily n).card = n := by
  rw [oneFamily, Finset.card_insert_of_notMem (oblique_not_verticalFamily (by omega)),
    verticalFamily_card]
  omega

lemma oneFamily_affine {n : ℕ} {l : Line} (hl : l ∈ oneFamily n) : IsAffineLine l := by
  simp only [oneFamily, Finset.mem_insert] at hl
  rcases hl with rfl | hl
  · exact ⟨1, -1, -(((n - 1 : ℕ) : ℝ)), by norm_num, rfl⟩
  · exact verticalFamily_affine hl

lemma oneFamily_cover {n : ℕ} (hn : n ≥ 3) : Covers n (oneFamily n) := by
  intro a b hab
  by_cases ha : a ≤ n - 1
  · refine ⟨affineLine 1 0 (-(a : ℝ)), ?_, ?_⟩
    · simp only [oneFamily, Finset.mem_insert]
      right
      simp only [verticalFamily, Finset.mem_image, Finset.mem_Icc]
      exact ⟨a, ⟨by omega, ha⟩, rfl⟩
    · norm_num [OnLine, affineLine]
  · have han : a = n := by omega
    have hb1 : b = 1 := by omega
    subst a
    subst b
    refine ⟨oblique n, by simp [oneFamily], ?_⟩
    simp only [OnLine, oblique, affineLine, Set.mem_setOf_eq]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
    ring

lemma oblique_special {n : ℕ} : IsSpecial (oblique n) := by
  exact affineLine_special (by norm_num) (by norm_num) (by norm_num)

lemma oneFamily_special_card {n : ℕ} (hn : n ≥ 3) :
    (by classical exact ((oneFamily n).filter IsSpecial).card) = 1 := by
  classical
  apply Finset.card_eq_one.mpr
  refine ⟨oblique n, ?_⟩
  apply Finset.ext
  intro l
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hsp⟩
    simp only [oneFamily, Finset.mem_insert] at hl
    rcases hl with hl | hl
    · exact hl
    · have hempty : (verticalFamily (n - 1)).filter IsSpecial = ∅ := by
        apply Finset.card_eq_zero.mp
        exact verticalFamily_special_card
      exfalso
      have hmem : l ∈ (verticalFamily (n - 1)).filter IsSpecial :=
        Finset.mem_filter.mpr ⟨hl, hsp⟩
      rw [hempty] at hmem
      simp at hmem
  · intro hl
    subst l
    exact ⟨by simp [oneFamily], oblique_special⟩

theorem main_theorem (n : ℕ) (hn : n ≥ 3) : {0, 1, 3} = { k | ∃ lines : Finset (Set (ℝ × ℝ)), (∀ line ∈ lines, ∃ a b c, ¬ (a = 0 ∧ b = 0) ∧ line = { v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0 }) ∧ lines.card = n ∧ (∀ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b ≤ n + 1 → ∃ (l : Set (ℝ × ℝ)), l ∈ lines ∧ ((a : ℝ), (b : ℝ)) ∈ l) ∧ ((lines.filter (fun l => ∃ a b c, l = { v : ℝ × ℝ | a * v.1 + b * v.2 + c = 0 } ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)).card = k) } := by
  classical
  apply Set.ext
  intro k
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · intro hk
    rcases hk with rfl | rfl | rfl
    · refine ⟨verticalFamily n, ?_, verticalFamily_card, ?_, ?_⟩
      · intro line hline
        rcases verticalFamily_affine hline with ⟨A, B, C, hnz, hcarrier⟩
        exact ⟨A, B, C, hnz, hcarrier⟩
      · intro a b hab
        obtain ⟨l, hl, hon⟩ := verticalFamily_cover (n := n) a b hab
        exact ⟨l, hl, hon⟩
      · exact verticalFamily_special_card
    · refine ⟨oneFamily n, ?_, oneFamily_card hn, ?_, ?_⟩
      · intro line hline
        rcases oneFamily_affine hline with ⟨A, B, C, hnz, hcarrier⟩
        exact ⟨A, B, C, hnz, hcarrier⟩
      · intro a b hab
        obtain ⟨l, hl, hon⟩ := oneFamily_cover hn a b hab
        exact ⟨l, hl, hon⟩
      · exact oneFamily_special_card hn
    · refine ⟨specialLines n, ?_, specialLines_card hn, ?_, ?_⟩
      · intro line hline
        rcases specialLines_affine hline with ⟨A, B, C, hnz, hcarrier⟩
        exact ⟨A, B, C, hnz, hcarrier⟩
      · intro a b hab
        obtain ⟨l, hl, hon⟩ := specialLines_cover hn a b hab
        exact ⟨l, hl, hon⟩
      · exact specialLines_special_card
  · rintro ⟨lines, haff, hcard, hcover, hk⟩
    have haff' : ∀ l ∈ lines, IsAffineLine l := by
      intro l hl
      rcases haff l hl with ⟨A, B, C, hnz, hcarrier⟩
      exact ⟨A, B, C, hnz, hcarrier⟩
    have hcover' : Covers n lines := by
      intro a b hab
      exact hcover a b hab
    have hclass := special_count_classification n hn lines hcard haff' hcover'
    have hspecial : (by classical exact (lines.filter IsSpecial).card) = k := by
      simpa only [IsSpecial, affineLine] using hk
    omega

end IMO2025P1
