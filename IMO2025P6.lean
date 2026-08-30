module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat

public section

set_option maxHeartbeats 1200000

namespace IMO2025P6

variable {n : ℕ}
abbrev Point (n : ℕ) := Fin n × Fin n
variable {all_black : Finset (Point n)}

section ProblemSetup
variable [NeZero n]
abbrev px (p : Point n) : ℕ := p.1.val
abbrev py (p : Point n) : ℕ := p.2.val

@[ext] structure Matilda (n : ℕ) [NeZero n] (all_black : Finset (Point n)) where
  x_min : ℕ
  x_max : ℕ
  y_min : ℕ
  y_max : ℕ
  h_x_le : x_min ≤ x_max
  h_y_le : y_min ≤ y_max
  h_x_bound : x_max < n
  h_y_bound : y_max < n
  h_disjoint : ∀ p ∈ all_black, ¬(x_min ≤ px p ∧ px p ≤ x_max ∧ y_min ≤ py p ∧ py p ≤ y_max)
@[simp]
def Matilda.mem (m : Matilda n all_black) (p : Point n) : Prop :=
  m.x_min ≤ px p ∧ px p ≤ m.x_max ∧ m.y_min ≤ py p ∧ py p ≤ m.y_max

def IsValidConfiguration (n : ℕ) [NeZero n]
  (all_black : Finset (Point n)) (partition : Finset (Matilda n all_black)) : Prop :=
  all_black.card = n ∧
  (∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q) ∧
  (∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q) ∧
  (∀ p : Point n, p ∉ all_black → ∃! m ∈ partition, m.mem p)

def IsMinMatildaCount (n : ℕ) [NeZero n] (m : ℕ) : Prop :=
  (∀ (all_black : Finset (Point n)) (partition : Finset (Matilda n all_black)),
      IsValidConfiguration n all_black partition → m ≤ partition.card) ∧
  (∃ (all_black : Finset (Point n)) (partition : Finset (Matilda n all_black)),
      IsValidConfiguration n all_black partition ∧ partition.card = m)

end ProblemSetup

abbrev solution_value : ℕ := 2112

private def blackPoint (i : Fin 2025) : Point 2025 :=
  (i, ⟨(2 * i.val) % 2025, Nat.mod_lt _ (by omega)⟩)

private def constructionBlack : Finset (Point 2025) :=
  Finset.univ.image blackPoint

private lemma constructionBlack_spec (p : Point 2025) :
    p ∈ constructionBlack ↔ py p = (2 * px p) % 2025 := by
  constructor
  · intro hp
    simp only [constructionBlack, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    rfl
  · intro hp
    simp only [constructionBlack, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨p.1, Prod.ext ?_ ?_⟩
    · rfl
    · apply Fin.ext
      exact hp.symm

private def constructionTile (x₁ x₂ y₁ y₂ : ℕ)
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) (hxb : x₂ < 2025) (hyb : y₂ < 2025)
    (hd : ∀ x, x₁ ≤ x → x ≤ x₂ → ¬(y₁ ≤ (2 * x) % 2025 ∧ (2 * x) % 2025 ≤ y₂)) :
    Matilda 2025 constructionBlack where
  x_min := x₁
  x_max := x₂
  y_min := y₁
  y_max := y₂
  h_x_le := hx
  h_y_le := hy
  h_x_bound := hxb
  h_y_bound := hyb
  h_disjoint := by
    intro p hp hmem
    rw [constructionBlack_spec] at hp
    exact hd (px p) hmem.1 hmem.2.1 ⟨by omega, by omega⟩

private def upperTile (j : Fin 1012) : Matilda 2025 constructionBlack :=
  constructionTile 0 j.val (2 * j.val + 1) (2 * j.val + 2)
    (by omega) (by omega) (by omega) (by omega) (by
      intro x hx₁ hx₂
      have hmod : (2 * x) % 2025 = 2 * x := Nat.mod_eq_of_lt (by omega)
      omega)

private def middleTile (j : Fin 1012) : Matilda 2025 constructionBlack :=
  constructionTile (j.val + 1) (1012 + j.val) (2 * j.val) (2 * j.val + 1)
    (by omega) (by omega) (by omega) (by omega) (by
      intro x hx₁ hx₂
      by_cases hx : x ≤ 1012
      · have hmod : (2 * x) % 2025 = 2 * x := Nat.mod_eq_of_lt (by omega)
        omega
      · have hxlt : x < 2025 := by omega
        have hmod : (2 * x) % 2025 = 2 * x - 2025 := by
          omega
        omega)

private def lowerTile (j : Fin 1011) : Matilda 2025 constructionBlack :=
  constructionTile (1014 + j.val) 2024 (2 * j.val + 1) (2 * j.val + 2)
    (by omega) (by omega) (by omega) (by omega) (by
      intro x hx₁ hx₂
      have hxlt : x < 2025 := by omega
      have hmod : (2 * x) % 2025 = 2 * x - 2025 := by omega
      omega)

private def leftTile : Matilda 2025 constructionBlack :=
  constructionTile 1013 2024 0 0
    (by omega) (by omega) (by omega) (by omega) (by
      intro x hx₁ hx₂
      have hxlt : x < 2025 := by omega
      have hmod : (2 * x) % 2025 = 2 * x - 2025 := by omega
      omega)

private def rightTile : Matilda 2025 constructionBlack :=
  constructionTile 1013 2024 2024 2024
    (by omega) (by omega) (by omega) (by omega) (by
      intro x hx₁ hx₂
      have hxlt : x < 2025 := by omega
      have hmod : (2 * x) % 2025 = 2 * x - 2025 := by omega
      omega)

private lemma upperTile_mem (j : Fin 1012) (p : Point 2025) :
    (upperTile j).mem p ↔ px p ≤ j.val ∧ 2 * j.val + 1 ≤ py p ∧ py p ≤ 2 * j.val + 2 := by
  simp [upperTile, constructionTile]

private lemma middleTile_mem (j : Fin 1012) (p : Point 2025) :
    (middleTile j).mem p ↔
      j.val + 1 ≤ px p ∧ px p ≤ 1012 + j.val ∧
      2 * j.val ≤ py p ∧ py p ≤ 2 * j.val + 1 := by
  simp [middleTile, constructionTile]

private lemma lowerTile_mem (j : Fin 1011) (p : Point 2025) :
    (lowerTile j).mem p ↔
      1014 + j.val ≤ px p ∧ 2 * j.val + 1 ≤ py p ∧ py p ≤ 2 * j.val + 2 := by
  have hpx : px p < 2025 := p.1.isLt
  simp [lowerTile, constructionTile]
  omega

private lemma leftTile_mem (p : Point 2025) :
    leftTile.mem p ↔ 1013 ≤ px p ∧ py p = 0 := by
  have hpx : px p < 2025 := p.1.isLt
  simp [leftTile, constructionTile]
  omega

private lemma rightTile_mem (p : Point 2025) :
    rightTile.mem p ↔ 1013 ≤ px p ∧ py p = 2024 := by
  have hpx : px p < 2025 := p.1.isLt
  simp [rightTile, constructionTile]
  omega

private lemma blackPoint_injective : Function.Injective blackPoint := by
  intro i j hij
  exact congrArg Prod.fst hij

private lemma constructionBlack_card : constructionBlack.card = 2025 := by
  rw [constructionBlack, Finset.card_image_of_injective _ blackPoint_injective]
  simp

private lemma upperTile_injective : Function.Injective upperTile := by
  intro i j hij
  have h := congrArg (fun m : Matilda 2025 constructionBlack => m.x_max) hij
  exact Fin.ext h

private lemma middleTile_injective : Function.Injective middleTile := by
  intro i j hij
  have h := congrArg (fun m : Matilda 2025 constructionBlack => m.x_min) hij
  apply Fin.ext
  simpa [middleTile, constructionTile] using h

private lemma lowerTile_injective : Function.Injective lowerTile := by
  intro i j hij
  have h := congrArg (fun m : Matilda 2025 constructionBlack => m.x_min) hij
  apply Fin.ext
  simpa [lowerTile, constructionTile] using h

private def tileCode (t : Matilda 2025 constructionBlack) : ℕ × ℕ × ℕ × ℕ :=
  (t.x_min, t.x_max, t.y_min, t.y_max)

private lemma tileCode_injective : Function.Injective tileCode := by
  intro a b h
  apply Matilda.ext
  · exact congrArg (fun z => z.1) h
  · exact congrArg (fun z => z.2.1) h
  · exact congrArg (fun z => z.2.2.1) h
  · exact congrArg (fun z => z.2.2.2) h

private instance : DecidableEq (Matilda 2025 constructionBlack) :=
  tileCode_injective.decidableEq

private def constructionPartition : Finset (Matilda 2025 constructionBlack) :=
  (Finset.univ.image upperTile ∪ Finset.univ.image middleTile) ∪
    Finset.univ.image lowerTile ∪ {leftTile, rightTile}

private lemma constructionPartition_mem (t : Matilda 2025 constructionBlack) :
    t ∈ constructionPartition ↔
      (∃ j, t = upperTile j) ∨ (∃ j, t = middleTile j) ∨
      (∃ j, t = lowerTile j) ∨ t = leftTile ∨ t = rightTile := by
  simp only [constructionPartition, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  aesop

private lemma construction_exists (p : Point 2025) (hp : p ∉ constructionBlack) :
    ∃ t ∈ constructionPartition, t.mem p := by
  have hxlt : px p < 2025 := p.1.isLt
  have hylt : py p < 2025 := p.2.isLt
  rw [constructionBlack_spec] at hp
  by_cases hx : px p ≤ 1012
  · have hmod : (2 * px p) % 2025 = 2 * px p := Nat.mod_eq_of_lt (by omega)
    by_cases hy : py p < 2 * px p
    · let j : Fin 1012 := ⟨py p / 2, by omega⟩
      refine ⟨middleTile j, ?_, (middleTile_mem j p).2 ?_⟩
      · rw [constructionPartition_mem]
        exact Or.inr (Or.inl ⟨j, rfl⟩)
      · dsimp [j]
        omega
    · let j : Fin 1012 := ⟨(py p - 1) / 2, by omega⟩
      refine ⟨upperTile j, ?_, (upperTile_mem j p).2 ?_⟩
      · rw [constructionPartition_mem]
        exact Or.inl ⟨j, rfl⟩
      · dsimp [j]
        omega
  · have hxlo : 1013 ≤ px p := by omega
    have hmod : (2 * px p) % 2025 = 2 * px p - 2025 := by omega
    by_cases hy : py p < 2 * px p - 2025
    · by_cases hy0 : py p = 0
      · refine ⟨leftTile, ?_, (leftTile_mem p).2 ⟨hxlo, hy0⟩⟩
        rw [constructionPartition_mem]
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · let j : Fin 1011 := ⟨(py p - 1) / 2, by omega⟩
        refine ⟨lowerTile j, ?_, (lowerTile_mem j p).2 ?_⟩
        · rw [constructionPartition_mem]
          exact Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))
        · dsimp [j]
          omega
    · by_cases hymax : py p = 2024
      · refine ⟨rightTile, ?_, (rightTile_mem p).2 ⟨hxlo, hymax⟩⟩
        rw [constructionPartition_mem]
        exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · let j : Fin 1012 := ⟨py p / 2, by omega⟩
        refine ⟨middleTile j, ?_, (middleTile_mem j p).2 ?_⟩
        · rw [constructionPartition_mem]
          exact Or.inr (Or.inl ⟨j, rfl⟩)
        · dsimp [j]
          omega

private lemma construction_unique (p : Point 2025)
    (a b : Matilda 2025 constructionBlack) (ha : a ∈ constructionPartition) (hb : b ∈ constructionPartition)
    (hap : a.mem p) (hbp : b.mem p) : a = b := by
  rw [constructionPartition_mem] at ha hb
  rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | rfl <;>
    rcases hb with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl
  · apply congrArg upperTile
    apply Fin.ext
    rw [upperTile_mem] at hap hbp
    omega
  · rw [upperTile_mem] at hap
    rw [middleTile_mem] at hbp
    omega
  · rw [upperTile_mem] at hap
    rw [lowerTile_mem] at hbp
    omega
  · rw [upperTile_mem] at hap
    rw [leftTile_mem] at hbp
    omega
  · rw [upperTile_mem] at hap
    rw [rightTile_mem] at hbp
    omega
  · rw [middleTile_mem] at hap
    rw [upperTile_mem] at hbp
    omega
  · apply congrArg middleTile
    apply Fin.ext
    rw [middleTile_mem] at hap hbp
    omega
  · rw [middleTile_mem] at hap
    rw [lowerTile_mem] at hbp
    omega
  · rw [middleTile_mem] at hap
    rw [leftTile_mem] at hbp
    omega
  · rw [middleTile_mem] at hap
    rw [rightTile_mem] at hbp
    omega
  · rw [lowerTile_mem] at hap
    rw [upperTile_mem] at hbp
    omega
  · rw [lowerTile_mem] at hap
    rw [middleTile_mem] at hbp
    omega
  · apply congrArg lowerTile
    apply Fin.ext
    rw [lowerTile_mem] at hap hbp
    omega
  · rw [lowerTile_mem] at hap
    rw [leftTile_mem] at hbp
    omega
  · rw [lowerTile_mem] at hap
    rw [rightTile_mem] at hbp
    omega
  · rw [leftTile_mem] at hap
    rw [upperTile_mem] at hbp
    omega
  · rw [leftTile_mem] at hap
    rw [middleTile_mem] at hbp
    omega
  · rw [leftTile_mem] at hap
    rw [lowerTile_mem] at hbp
    omega
  · rfl
  · rw [leftTile_mem] at hap
    rw [rightTile_mem] at hbp
    omega
  · rw [rightTile_mem] at hap
    rw [upperTile_mem] at hbp
    omega
  · rw [rightTile_mem] at hap
    rw [middleTile_mem] at hbp
    omega
  · rw [rightTile_mem] at hap
    rw [lowerTile_mem] at hbp
    omega
  · rw [rightTile_mem] at hap
    rw [leftTile_mem] at hbp
    omega
  · rfl

private lemma constructionPartition_card : constructionPartition.card = 3037 := by
  classical
  let U : Finset (Matilda 2025 constructionBlack) := Finset.univ.image upperTile
  let M : Finset (Matilda 2025 constructionBlack) := Finset.univ.image middleTile
  let L : Finset (Matilda 2025 constructionBlack) := Finset.univ.image lowerTile
  have hU : U.card = 1012 := by
    rw [show U = Finset.univ.image upperTile by rfl,
      Finset.card_image_of_injective _ upperTile_injective]
    simp
  have hM : M.card = 1012 := by
    rw [show M = Finset.univ.image middleTile by rfl,
      Finset.card_image_of_injective _ middleTile_injective]
    simp
  have hL : L.card = 1011 := by
    rw [show L = Finset.univ.image lowerTile by rfl,
      Finset.card_image_of_injective _ lowerTile_injective]
    simp
  have hUM : Disjoint U M := by
    rw [Finset.disjoint_left]
    intro t htU htM
    simp only [U, Finset.mem_image, Finset.mem_univ, true_and] at htU
    simp only [M, Finset.mem_image, Finset.mem_univ, true_and] at htM
    obtain ⟨i, rfl⟩ := htU
    obtain ⟨j, h⟩ := htM
    have hx := congrArg (fun t : Matilda 2025 constructionBlack => t.x_min) h
    simp [upperTile, middleTile, constructionTile] at hx
  have hUL : Disjoint U L := by
    rw [Finset.disjoint_left]
    intro t htU htL
    simp only [U, Finset.mem_image, Finset.mem_univ, true_and] at htU
    simp only [L, Finset.mem_image, Finset.mem_univ, true_and] at htL
    obtain ⟨i, rfl⟩ := htU
    obtain ⟨j, h⟩ := htL
    have hx := congrArg (fun t : Matilda 2025 constructionBlack => t.x_min) h
    simp [upperTile, lowerTile, constructionTile] at hx
  have hML : Disjoint M L := by
    rw [Finset.disjoint_left]
    intro t htM htL
    simp only [M, Finset.mem_image, Finset.mem_univ, true_and] at htM
    simp only [L, Finset.mem_image, Finset.mem_univ, true_and] at htL
    obtain ⟨i, rfl⟩ := htM
    obtain ⟨j, h⟩ := htL
    have hx := congrArg (fun t : Matilda 2025 constructionBlack => t.x_min) h
    simp [middleTile, lowerTile, constructionTile] at hx
    omega
  have hU_left : leftTile ∉ U := by
    intro h
    simp only [U, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨i, h⟩ := h
    have hx := congrArg (fun t : Matilda 2025 constructionBlack => t.x_min) h
    simp [upperTile, leftTile, constructionTile] at hx
  have hM_left : leftTile ∉ M := by
    intro h
    simp only [M, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨i, h⟩ := h
    have hy := congrArg (fun t : Matilda 2025 constructionBlack => t.y_max) h
    simp [middleTile, leftTile, constructionTile] at hy
  have hL_left : leftTile ∉ L := by
    intro h
    simp only [L, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨i, h⟩ := h
    have hx := congrArg (fun t : Matilda 2025 constructionBlack => t.x_min) h
    simp [lowerTile, leftTile, constructionTile] at hx
    omega
  have hU_right : rightTile ∉ U := by
    intro h
    simp only [U, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨i, h⟩ := h
    have hx := congrArg (fun t : Matilda 2025 constructionBlack => t.x_min) h
    simp [upperTile, rightTile, constructionTile] at hx
  have hM_right : rightTile ∉ M := by
    intro h
    simp only [M, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨i, h⟩ := h
    have hy := congrArg (fun t : Matilda 2025 constructionBlack => t.y_max) h
    simp [middleTile, rightTile, constructionTile] at hy
    omega
  have hL_right : rightTile ∉ L := by
    intro h
    simp only [L, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨i, h⟩ := h
    have hx := congrArg (fun t : Matilda 2025 constructionBlack => t.x_min) h
    simp [lowerTile, rightTile, constructionTile] at hx
    omega
  have hlr : leftTile ≠ rightTile := by
    intro h
    have hy := congrArg (fun t : Matilda 2025 constructionBlack => t.y_min) h
    simp [leftTile, rightTile, constructionTile] at hy
  have hUML : (U ∪ M ∪ L).card = 3035 := by
    rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hUL, hML⟩),
      Finset.card_union_of_disjoint hUM, hU, hM, hL]
  have hdlast : Disjoint (U ∪ M ∪ L) {leftTile, rightTile} := by
    simp only [Finset.disjoint_insert_right, Finset.disjoint_singleton_right,
      Finset.mem_union, not_or]
    exact ⟨⟨⟨hU_left, hM_left⟩, hL_left⟩,
      ⟨⟨hU_right, hM_right⟩, hL_right⟩⟩
  change (U ∪ M ∪ L ∪ {leftTile, rightTile}).card = 3037
  rw [Finset.card_union_of_disjoint hdlast, hUML]
  simp [hlr]

private lemma constructionBlack_x_unique (p q : Point 2025)
    (hp : p ∈ constructionBlack) (hq : q ∈ constructionBlack) (h : px p = px q) : p = q := by
  apply Prod.ext
  · apply Fin.ext
    exact h
  · rw [constructionBlack_spec] at hp hq
    apply Fin.ext
    calc
      py p = (2 * px p) % 2025 := hp
      _ = (2 * px q) % 2025 := by rw [h]
      _ = py q := hq.symm

private lemma double_mod_injective {a b : ℕ} (ha : a < 2025) (hb : b < 2025)
    (h : (2 * a) % 2025 = (2 * b) % 2025) : a = b := by
  have hmod : 2 * a ≡ 2 * b [MOD 2025] := h
  have hgcd : Nat.gcd 2025 2 = 1 := by decide
  have hab : a ≡ b [MOD 2025] := Nat.ModEq.cancel_left_of_coprime hgcd hmod
  omega

private lemma constructionBlack_y_unique (p q : Point 2025)
    (hp : p ∈ constructionBlack) (hq : q ∈ constructionBlack) (h : py p = py q) : p = q := by
  apply Prod.ext
  · rw [constructionBlack_spec] at hp hq
    apply Fin.ext
    apply double_mod_injective p.1.isLt q.1.isLt
    calc
      (2 * px p) % 2025 = py p := hp.symm
      _ = py q := h
      _ = (2 * px q) % 2025 := hq
  · apply Fin.ext
    exact h

private lemma construction_valid :
    IsValidConfiguration 2025 constructionBlack constructionPartition := by
  refine ⟨constructionBlack_card, ?_, ?_, ?_⟩
  · intro p hp q hq h
    exact constructionBlack_x_unique p q hp hq h
  · intro p hp q hq h
    exact constructionBlack_y_unique p q hp hq h
  intro p hp
  obtain ⟨t, ht, htp⟩ := construction_exists p hp
  refine ⟨t, ⟨ht, htp⟩, ?_⟩
  intro u hu
  exact construction_unique p u t hu.1 ht hu.2 htp

private lemma construction_upper_bound :
    ∃ (all_black : Finset (Point 2025)) (partition : Finset (Matilda 2025 all_black)),
      IsValidConfiguration 2025 all_black partition ∧ partition.card = 3037 := by
  exact ⟨constructionBlack, constructionPartition, construction_valid,
    constructionPartition_card⟩

private inductive GridTag where
  | Face (u v : Fin 44)
  | North (a : Fin 44)
  | South (t : Fin 44)
  | West (t : Fin 44)
  | East (t : Fin 44)
  deriving DecidableEq, Fintype

private def gridHole (z : Fin 45 × Fin 45) : Point 2025 :=
  (⟨45 * z.1.val + z.2.val, by omega⟩,
    ⟨45 * z.2.val + 44 - z.1.val, by omega⟩)

private def gridBlack : Finset (Point 2025) :=
  Finset.univ.image gridHole

private lemma gridBlack_spec (p : Point 2025) :
    p ∈ gridBlack ↔ ∃ r a : Fin 45,
      px p = 45 * r.val + a.val ∧ py p = 45 * a.val + 44 - r.val := by
  constructor
  · simp only [gridBlack, Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨⟨r, a⟩, rfl⟩
    exact ⟨r, a, rfl, rfl⟩
  · rintro ⟨r, a, hx, hy⟩
    simp only [gridBlack, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨(r, a), ?_⟩
    apply Prod.ext
    · apply Fin.ext
      exact hx.symm
    · apply Fin.ext
      exact hy.symm

private lemma gridHole_injective : Function.Injective gridHole := by
  rintro ⟨r, a⟩ ⟨s, b⟩ h
  have hx := congrArg (fun p : Point 2025 => px p) h
  change 45 * r.val + a.val = 45 * s.val + b.val at hx
  have hrs : r.val = s.val := by omega
  have hab : a.val = b.val := by omega
  exact Prod.ext (Fin.ext hrs) (Fin.ext hab)

private lemma gridBlack_card : gridBlack.card = 2025 := by
  rw [gridBlack, Finset.card_image_of_injective _ gridHole_injective]
  norm_num

private lemma gridBlack_x_unique (p q : Point 2025)
    (hp : p ∈ gridBlack) (hq : q ∈ gridBlack) (h : px p = px q) : p = q := by
  rw [gridBlack_spec] at hp hq
  obtain ⟨r, a, hpx, hpy⟩ := hp
  obtain ⟨s, b, hqx, hqy⟩ := hq
  have hrs : r.val = s.val := by omega
  have hab : a.val = b.val := by omega
  have hy : py p = py q := by
    rw [hpy, hqy, hrs, hab]
  exact Prod.ext (Fin.ext h) (Fin.ext hy)

private lemma gridBlack_y_unique (p q : Point 2025)
    (hp : p ∈ gridBlack) (hq : q ∈ gridBlack) (h : py p = py q) : p = q := by
  rw [gridBlack_spec] at hp hq
  obtain ⟨r, a, hpx, hpy⟩ := hp
  obtain ⟨s, b, hqx, hqy⟩ := hq
  have hab : a.val = b.val := by omega
  have hrs : r.val = s.val := by omega
  have hx : px p = px q := by
    rw [hpx, hqx, hrs, hab]
  exact Prod.ext (Fin.ext hx) (Fin.ext h)

private def gridRect (x₁ x₂ y₁ y₂ : ℕ)
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) (hxb : x₂ < 2025) (hyb : y₂ < 2025)
    (hd : ∀ r a : Fin 45,
      ¬(x₁ ≤ 45 * r.val + a.val ∧ 45 * r.val + a.val ≤ x₂ ∧
        y₁ ≤ 45 * a.val + 44 - r.val ∧ 45 * a.val + 44 - r.val ≤ y₂)) :
    Matilda 2025 gridBlack where
  x_min := x₁
  x_max := x₂
  y_min := y₁
  y_max := y₂
  h_x_le := hx
  h_y_le := hy
  h_x_bound := hxb
  h_y_bound := hyb
  h_disjoint := by
    intro p hp hmem
    rw [gridBlack_spec] at hp
    obtain ⟨r, a, hpx, hpy⟩ := hp
    apply hd r a
    rw [← hpx, ← hpy]
    exact hmem

private def gridTile : GridTag → Matilda 2025 gridBlack
  | .Face u v =>
      gridRect (45 * u.val + v.val + 1) (45 * (u.val + 1) + v.val)
        (45 * v.val + 44 - u.val) (45 * (v.val + 1) + 43 - u.val)
        (by omega) (by omega) (by omega) (by omega) (by
          intro r a h
          rcases h with ⟨hxlo, hxhi, hylo, hyhi⟩
          have hcase :
              (r.val = u.val ∧ v.val < a.val) ∨
                (r.val = u.val + 1 ∧ a.val ≤ v.val) := by
            omega
          rcases hcase with ⟨hru, hva⟩ | ⟨hru, hav⟩
          · omega
          · omega)
  | .North a =>
      gridRect a.val a.val (45 * (a.val + 1)) 2024
        (by omega) (by omega) (by omega) (by omega) (by
          intro r b h
          rcases h with ⟨hxlo, hxhi, hylo, hyhi⟩
          omega)
  | .South t =>
      gridRect (1981 + t.val) (1981 + t.val) 0 (45 * (t.val + 1) - 1)
        (by omega) (by omega) (by omega) (by omega) (by
          intro r a h
          rcases h with ⟨hxlo, hxhi, hylo, hyhi⟩
          omega)
  | .West t =>
      gridRect 0 (45 * (t.val + 1) - 1) (43 - t.val) (43 - t.val)
        (by omega) (by omega) (by omega) (by omega) (by
          intro r a h
          rcases h with ⟨hxlo, hxhi, hylo, hyhi⟩
          omega)
  | .East t =>
      gridRect (45 * (t.val + 1)) 2024 (2024 - t.val) (2024 - t.val)
        (by omega) (by omega) (by omega) (by omega) (by
          intro r a h
          rcases h with ⟨hxlo, hxhi, hylo, hyhi⟩
          omega)

private lemma gridTile_injective : Function.Injective gridTile := by
  intro t u h
  have hx₁ := congrArg (fun m : Matilda 2025 gridBlack => m.x_min) h
  have hx₂ := congrArg (fun m : Matilda 2025 gridBlack => m.x_max) h
  have hy₁ := congrArg (fun m : Matilda 2025 gridBlack => m.y_min) h
  have hy₂ := congrArg (fun m : Matilda 2025 gridBlack => m.y_max) h
  rcases t with ⟨a, b⟩ | a | a | a | a <;>
    rcases u with ⟨c, d⟩ | c | c | c | c <;>
    simp only [gridTile, gridRect] at hx₁ hx₂ hy₁ hy₂
  · exact congrArg₂ GridTag.Face (Fin.ext (by omega)) (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact congrArg GridTag.North (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact congrArg GridTag.South (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact congrArg GridTag.West (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact congrArg GridTag.East (Fin.ext (by omega))

private def gridTileCode (t : Matilda 2025 gridBlack) : ℕ × ℕ × ℕ × ℕ :=
  (t.x_min, t.x_max, t.y_min, t.y_max)

private lemma gridTileCode_injective : Function.Injective gridTileCode := by
  intro a b h
  apply Matilda.ext
  · exact congrArg (fun z => z.1) h
  · exact congrArg (fun z => z.2.1) h
  · exact congrArg (fun z => z.2.2.1) h
  · exact congrArg (fun z => z.2.2.2) h

private instance : DecidableEq (Matilda 2025 gridBlack) :=
  gridTileCode_injective.decidableEq

private def gridPartition : Finset (Matilda 2025 gridBlack) :=
  Finset.univ.image gridTile

private lemma gridPartition_mem (m : Matilda 2025 gridBlack) :
    m ∈ gridPartition ↔ ∃ t : GridTag, m = gridTile t := by
  simp only [gridPartition, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

private def gridTagEquiv : GridTag ≃
    ((Fin 44 × Fin 44) ⊕ (Fin 44 ⊕ (Fin 44 ⊕ (Fin 44 ⊕ Fin 44)))) where
  toFun
    | .Face u v => Sum.inl (u, v)
    | .North a => Sum.inr (Sum.inl a)
    | .South t => Sum.inr (Sum.inr (Sum.inl t))
    | .West t => Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))
    | .East t => Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))
  invFun
    | Sum.inl (u, v) => .Face u v
    | Sum.inr (Sum.inl a) => .North a
    | Sum.inr (Sum.inr (Sum.inl t)) => .South t
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => .West t
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr t))) => .East t
  left_inv := by
    intro t
    cases t <;> rfl
  right_inv := by
    intro t
    rcases t with ⟨u, v⟩ | a | t | t | t <;> rfl

private lemma gridTag_card : Fintype.card GridTag = (44 * 44) + 4 * 44 := by
  rw [Fintype.card_congr gridTagEquiv]
  norm_num

private lemma gridPartition_card : gridPartition.card = 2112 := by
  calc
    gridPartition.card = Fintype.card GridTag := by
      rw [gridPartition, Finset.card_image_of_injective _ gridTile_injective]
      simp
    _ = (44 * 44) + 4 * 44 := gridTag_card
    _ = 2112 := by norm_num

private lemma gridTile_unique (p : Point 2025) (t u : GridTag)
    (ht : (gridTile t).mem p) (hu : (gridTile u).mem p) : t = u := by
  rcases t with ⟨a, b⟩ | a | a | a | a <;>
    rcases u with ⟨c, d⟩ | c | c | c | c <;>
    simp only [gridTile, gridRect, Matilda.mem] at ht hu
  · exact congrArg₂ GridTag.Face (Fin.ext (by omega)) (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact congrArg GridTag.North (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact congrArg GridTag.South (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact congrArg GridTag.West (Fin.ext (by omega))
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact congrArg GridTag.East (Fin.ext (by omega))

private lemma grid_exists (p : Point 2025) (hp : p ∉ gridBlack) :
    ∃ m ∈ gridPartition, m.mem p := by
  let r := px p / 45
  let a := px p % 45
  let b := py p / 45
  let s := 44 - py p % 45
  have hxmod := Nat.mod_add_div (px p) 45
  have hymod := Nat.mod_add_div (py p) 45
  have hxrem : px p % 45 < 45 := Nat.mod_lt _ (by omega)
  have hyrem : py p % 45 < 45 := Nat.mod_lt _ (by omega)
  have hxlt : px p < 2025 := p.1.isLt
  have hylt : py p < 2025 := p.2.isLt
  have hr : r < 45 := by
    dsimp [r]
    omega
  have ha : a < 45 := by
    exact hxrem
  have hb : b < 45 := by
    dsimp [b]
    omega
  have hs : s < 45 := by
    dsimp [s]
    omega
  have hx : px p = 45 * r + a := by
    dsimp [r, a]
    omega
  have hy : py p = 45 * b + (44 - s) := by
    dsimp [b, s]
    omega
  have hnot : ¬(a = b ∧ s = r) := by
    rintro ⟨hab, hsr⟩
    apply hp
    rw [gridBlack_spec]
    refine ⟨⟨r, hr⟩, ⟨a, ha⟩, hx, ?_⟩
    have hyr : py p = 45 * a + 44 - r := by omega
    exact hyr
  by_cases hba : b < a
  · by_cases hsr : s ≤ r
    · by_cases hr44 : r = 44
      · let t : Fin 44 := ⟨a - 1, by omega⟩
        refine ⟨gridTile (.South t), ?_, ?_⟩
        · rw [gridPartition_mem]
          exact ⟨.South t, rfl⟩
        · simp only [gridTile, gridRect, Matilda.mem]
          dsimp [t]
          omega
      · let u : Fin 44 := ⟨r, by omega⟩
        let v : Fin 44 := ⟨b, by omega⟩
        refine ⟨gridTile (.Face u v), ?_, ?_⟩
        · rw [gridPartition_mem]
          exact ⟨.Face u v, rfl⟩
        · simp only [gridTile, gridRect, Matilda.mem]
          dsimp [u, v]
          omega
    · have hrs : r < s := by omega
      by_cases hb0 : b = 0
      · let t : Fin 44 := ⟨s - 1, by omega⟩
        refine ⟨gridTile (.West t), ?_, ?_⟩
        · rw [gridPartition_mem]
          exact ⟨.West t, rfl⟩
        · simp only [gridTile, gridRect, Matilda.mem]
          dsimp [t]
          omega
      · let u : Fin 44 := ⟨r, by omega⟩
        let v : Fin 44 := ⟨b - 1, by omega⟩
        refine ⟨gridTile (.Face u v), ?_, ?_⟩
        · rw [gridPartition_mem]
          exact ⟨.Face u v, rfl⟩
        · simp only [gridTile, gridRect, Matilda.mem]
          dsimp [u, v]
          omega
  · have hab : a ≤ b := by omega
    by_cases hsr : s < r
    · by_cases hb44 : b = 44
      · let t : Fin 44 := ⟨s, by omega⟩
        refine ⟨gridTile (.East t), ?_, ?_⟩
        · rw [gridPartition_mem]
          exact ⟨.East t, rfl⟩
        · simp only [gridTile, gridRect, Matilda.mem]
          dsimp [t]
          omega
      · let u : Fin 44 := ⟨r - 1, by omega⟩
        let v : Fin 44 := ⟨b, by omega⟩
        refine ⟨gridTile (.Face u v), ?_, ?_⟩
        · rw [gridPartition_mem]
          exact ⟨.Face u v, rfl⟩
        · simp only [gridTile, gridRect, Matilda.mem]
          dsimp [u, v]
          omega
    · have hrs : r ≤ s := by omega
      by_cases hab' : a < b
      · by_cases hr0 : r = 0
        · let t : Fin 44 := ⟨a, by omega⟩
          refine ⟨gridTile (.North t), ?_, ?_⟩
          · rw [gridPartition_mem]
            exact ⟨.North t, rfl⟩
          · simp only [gridTile, gridRect, Matilda.mem]
            dsimp [t]
            omega
        · let u : Fin 44 := ⟨r - 1, by omega⟩
          let v : Fin 44 := ⟨b - 1, by omega⟩
          refine ⟨gridTile (.Face u v), ?_, ?_⟩
          · rw [gridPartition_mem]
            exact ⟨.Face u v, rfl⟩
          · simp only [gridTile, gridRect, Matilda.mem]
            dsimp [u, v]
            omega
      · have habEq : a = b := by omega
        have hrs' : r < s := by
          by_contra h
          apply hnot
          exact ⟨habEq, by omega⟩
        by_cases hb0 : b = 0
        · let t : Fin 44 := ⟨s - 1, by omega⟩
          refine ⟨gridTile (.West t), ?_, ?_⟩
          · rw [gridPartition_mem]
            exact ⟨.West t, rfl⟩
          · simp only [gridTile, gridRect, Matilda.mem]
            dsimp [t]
            omega
        · let u : Fin 44 := ⟨r, by omega⟩
          let v : Fin 44 := ⟨b - 1, by omega⟩
          refine ⟨gridTile (.Face u v), ?_, ?_⟩
          · rw [gridPartition_mem]
            exact ⟨.Face u v, rfl⟩
          · simp only [gridTile, gridRect, Matilda.mem]
            dsimp [u, v]
            omega

private lemma grid_valid : IsValidConfiguration 2025 gridBlack gridPartition := by
  refine ⟨gridBlack_card, ?_, ?_, ?_⟩
  · intro p hp q hq h
    exact gridBlack_x_unique p q hp hq h
  · intro p hp q hq h
    exact gridBlack_y_unique p q hp hq h
  · intro p hp
    obtain ⟨m, hm, hmp⟩ := grid_exists p hp
    refine ⟨m, ⟨hm, hmp⟩, ?_⟩
    intro u hu
    rw [gridPartition_mem] at hm hu
    obtain ⟨t, rfl⟩ := hm
    obtain ⟨v, rfl⟩ := hu.1
    exact congrArg gridTile (gridTile_unique p v t hu.2 hmp)

lemma grid_construction_upper_bound :
    ∃ (all_black : Finset (Point 2025)) (partition : Finset (Matilda 2025 all_black)),
      IsValidConfiguration 2025 all_black partition ∧ partition.card = 2112 := by
  exact ⟨gridBlack, gridPartition, grid_valid, gridPartition_card⟩

set_option maxRecDepth 20000

/-! ## The universal lower bound

For the lower bound we regard every black square as a singleton rectangle.  An
`Owner` is either that singleton or one of the given white rectangles.  The
local seam counts below only use equality of owners; the lemmas immediately
following the definition record the rectangle-closure property that makes the
local counting possible.
-/

private abbrev Owner (all_black : Finset (Point 2025))
    (partition : Finset (Matilda 2025 all_black)) :=
  (↥all_black) ⊕ (↥partition)

private noncomputable def configurationOwner
    (all_black : Finset (Point 2025))
    (partition : Finset (Matilda 2025 all_black))
    (hvalid : IsValidConfiguration 2025 all_black partition) (p : Point 2025) :
    Owner all_black partition :=
  if hp : p ∈ all_black then
    Sum.inl ⟨p, hp⟩
  else
    Sum.inr ⟨Classical.choose (hvalid.2.2.2 p hp),
      (Classical.choose_spec (hvalid.2.2.2 p hp)).1.1⟩

private lemma configurationOwner_of_black
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    {p : Point 2025} (hp : p ∈ all_black) :
    configurationOwner all_black partition hvalid p = Sum.inl ⟨p, hp⟩ := by
  simp [configurationOwner, hp]

private lemma configurationOwner_left_iff
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (p : Point 2025) (b : ↥all_black) :
    configurationOwner all_black partition hvalid p = Sum.inl b ↔ p = b.1 := by
  constructor
  · intro h
    by_cases hp : p ∈ all_black
    · rw [configurationOwner_of_black hvalid hp] at h
      exact congrArg Subtype.val (Sum.inl.inj h)
    · simp [configurationOwner, hp] at h
  · intro h
    subst p
    simpa using configurationOwner_of_black hvalid b.2

private lemma configurationOwner_right_iff
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (p : Point 2025) (m : ↥partition) :
    configurationOwner all_black partition hvalid p = Sum.inr m ↔ m.1.mem p := by
  classical
  constructor
  · intro h
    by_cases hp : p ∈ all_black
    · rw [configurationOwner_of_black hvalid hp] at h
      simp at h
    · simp only [configurationOwner, dif_neg hp] at h
      have hm : (⟨Classical.choose (hvalid.2.2.2 p hp),
          (Classical.choose_spec (hvalid.2.2.2 p hp)).1.1⟩ : ↥partition) = m :=
        Sum.inr.inj h
      rw [← hm]
      exact (Classical.choose_spec (hvalid.2.2.2 p hp)).1.2
  · intro hmp
    have hp : p ∉ all_black := by
      intro hp
      exact m.1.h_disjoint p hp hmp
    simp only [configurationOwner, dif_neg hp]
    apply congrArg Sum.inr
    apply Subtype.ext
    exact ((Classical.choose_spec (hvalid.2.2.2 p hp)).2 m.1 ⟨m.2, hmp⟩).symm

private lemma configurationOwner_rectangle
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (p q : Point 2025)
    (hown : configurationOwner all_black partition hvalid p =
      configurationOwner all_black partition hvalid q) :
    configurationOwner all_black partition hvalid (p.1, q.2) =
        configurationOwner all_black partition hvalid p ∧
      configurationOwner all_black partition hvalid (q.1, p.2) =
        configurationOwner all_black partition hvalid p := by
  classical
  generalize hop : configurationOwner all_black partition hvalid p = o
  have hoq : configurationOwner all_black partition hvalid q = o := by
    rw [← hown, hop]
  cases o with
  | inl b =>
      have hp : p = b.1 :=
        (configurationOwner_left_iff hvalid p b).1 hop
      have hq : q = b.1 :=
        (configurationOwner_left_iff hvalid q b).1 hoq
      subst p
      subst q
      simp [hop]
  | inr m =>
      have hp : m.1.mem p :=
        (configurationOwner_right_iff hvalid p m).1 hop
      have hq : m.1.mem q :=
        (configurationOwner_right_iff hvalid q m).1 hoq
      have hpq : m.1.mem (p.1, q.2) := by
        exact ⟨hp.1, hp.2.1, hq.2.2.1, hq.2.2.2⟩
      have hqp : m.1.mem (q.1, p.2) := by
        exact ⟨hq.1, hq.2.1, hp.2.2.1, hp.2.2.2⟩
      constructor
      · exact (configurationOwner_right_iff hvalid (p.1, q.2) m).2 hpq
      · exact (configurationOwner_right_iff hvalid (q.1, p.2) m).2 hqp

private noncomputable def ownerCorner
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)} :
    Owner all_black partition → Point 2025
  | Sum.inl b => b.1
  | Sum.inr m =>
      (⟨m.1.x_min, lt_of_le_of_lt m.1.h_x_le m.1.h_x_bound⟩,
       ⟨m.1.y_min, lt_of_le_of_lt m.1.h_y_le m.1.h_y_bound⟩)

private def IsOwnerTopLeft {α : Type}
    (owner : Point 2025 → α) (p : Point 2025) : Prop :=
  (∀ q : Point 2025, px q + 1 = px p → py q = py p → owner q ≠ owner p) ∧
  (∀ q : Point 2025, px q = px p → py q + 1 = py p → owner q ≠ owner p)

private lemma ownerCorner_owned
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (o : Owner all_black partition) :
    configurationOwner all_black partition hvalid (ownerCorner o) = o := by
  classical
  cases o with
  | inl b =>
      simpa [ownerCorner] using configurationOwner_of_black hvalid b.2
  | inr m =>
      apply (configurationOwner_right_iff hvalid _ m).2
      simp only [ownerCorner]
      exact ⟨le_rfl, m.1.h_x_le, le_rfl, m.1.h_y_le⟩

private lemma ownerCorner_isTopLeft
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (o : Owner all_black partition) :
    IsOwnerTopLeft (configurationOwner all_black partition hvalid) (ownerCorner o) := by
  classical
  constructor
  · intro q hx hy hq
    cases o with
    | inl b =>
        have hqb : q = b.1 :=
          (configurationOwner_left_iff hvalid q b).1
            (hq.trans (ownerCorner_owned hvalid (Sum.inl b)))
        subst q
        simp [ownerCorner] at hx
    | inr m =>
        have hqm : m.1.mem q :=
          (configurationOwner_right_iff hvalid q m).1
            (hq.trans (ownerCorner_owned hvalid (Sum.inr m)))
        change px q + 1 = m.1.x_min at hx
        exact (Nat.not_succ_le_self (px q)) (hx.le.trans hqm.1)
  · intro q hx hy hq
    cases o with
    | inl b =>
        have hqb : q = b.1 :=
          (configurationOwner_left_iff hvalid q b).1
            (hq.trans (ownerCorner_owned hvalid (Sum.inl b)))
        subst q
        simp [ownerCorner] at hy
    | inr m =>
        have hqm : m.1.mem q :=
          (configurationOwner_right_iff hvalid q m).1
            (hq.trans (ownerCorner_owned hvalid (Sum.inr m)))
        change py q + 1 = m.1.y_min at hy
        exact (Nat.not_succ_le_self (py q)) (hy.le.trans hqm.2.2.1)

private lemma topLeft_eq_ownerCorner
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (p : Point 2025)
    (htl : IsOwnerTopLeft (configurationOwner all_black partition hvalid) p) :
    p = ownerCorner (configurationOwner all_black partition hvalid p) := by
  classical
  generalize hop : configurationOwner all_black partition hvalid p = o
  cases o with
  | inl b =>
      have hp : p = b.1 :=
        (configurationOwner_left_iff hvalid p b).1 hop
      simpa [ownerCorner] using hp
  | inr m =>
      have hmp : m.1.mem p :=
        (configurationOwner_right_iff hvalid p m).1 hop
      have hx : px p = m.1.x_min := by
        apply le_antisymm
        · by_contra hnot
          have hlt : m.1.x_min < px p := lt_of_not_ge hnot
          have hpxlt : px p < 2025 := p.1.isLt
          let q : Point 2025 :=
            (⟨px p - 1, by omega⟩, p.2)
          have hqx : px q = px p - 1 := by rfl
          have hqy : py q = py p := by rfl
          have hqm : m.1.mem q := by
            refine ⟨?_, ?_, hmp.2.2.1, hmp.2.2.2⟩
            · rw [hqx]
              omega
            · rw [hqx]
              exact (Nat.sub_le (px p) 1).trans hmp.2.1
          have hqo : configurationOwner all_black partition hvalid q =
              configurationOwner all_black partition hvalid p := by
            rw [(configurationOwner_right_iff hvalid q m).2 hqm, hop]
          exact htl.1 q (by omega) hqy hqo
        · exact hmp.1
      have hy : py p = m.1.y_min := by
        apply le_antisymm
        · by_contra hnot
          have hlt : m.1.y_min < py p := lt_of_not_ge hnot
          have hpylt : py p < 2025 := p.2.isLt
          let q : Point 2025 :=
            (p.1, ⟨py p - 1, by omega⟩)
          have hqx : px q = px p := by rfl
          have hqy : py q = py p - 1 := by rfl
          have hqm : m.1.mem q := by
            refine ⟨hmp.1, hmp.2.1, ?_, ?_⟩
            · rw [hqy]
              omega
            · rw [hqy]
              exact (Nat.sub_le (py p) 1).trans hmp.2.2.2
          have hqo : configurationOwner all_black partition hvalid q =
              configurationOwner all_black partition hvalid p := by
            rw [(configurationOwner_right_iff hvalid q m).2 hqm, hop]
          exact htl.2 q hqx (by omega) hqo
        · exact hmp.2.2.1
      apply Prod.ext
      · apply Fin.ext
        simpa [ownerCorner] using hx
      · apply Fin.ext
        simpa [ownerCorner] using hy

private noncomputable def ownerTopLefts
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) : Finset (Point 2025) := by
  classical
  exact Finset.univ.filter
    (IsOwnerTopLeft (configurationOwner all_black partition hvalid))

private lemma ownerCorner_injective
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Function.Injective (@ownerCorner all_black partition) := by
  intro a b hab
  rw [← ownerCorner_owned hvalid a, ← ownerCorner_owned hvalid b, hab]

private lemma ownerTopLefts_eq_image
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    ownerTopLefts hvalid = Finset.univ.image (@ownerCorner all_black partition) := by
  classical
  ext p
  simp only [ownerTopLefts, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hp
    exact ⟨configurationOwner all_black partition hvalid p,
      (topLeft_eq_ownerCorner hvalid p hp).symm⟩
  · rintro ⟨o, rfl⟩
    exact ownerCorner_isTopLeft hvalid o

private lemma ownerTopLefts_card
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    (ownerTopLefts hvalid).card = all_black.card + partition.card := by
  classical
  rw [ownerTopLefts_eq_image hvalid,
    Finset.card_image_of_injective _ (ownerCorner_injective hvalid)]
  simp

private def HasRectangleClosure {α : Type} (owner : Point 2025 → α) : Prop :=
  ∀ p q, owner p = owner q →
    owner (p.1, q.2) = owner p ∧ owner (q.1, p.2) = owner p

private lemma configurationOwner_hasRectangleClosure
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    HasRectangleClosure (configurationOwner all_black partition hvalid) :=
  configurationOwner_rectangle hvalid

/-! ### The black permutation -/

private lemma blackX_bijective
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Function.Bijective (fun p : ↥all_black => p.1.1) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro p q hpq
    apply Subtype.ext
    exact hvalid.2.1 p.1 p.2 q.1 q.2 (congrArg Fin.val hpq)
  · simpa using hvalid.1

private noncomputable def blackXEquiv
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    ↥all_black ≃ Fin 2025 :=
  Equiv.ofBijective (fun p : ↥all_black => p.1.1) (blackX_bijective hvalid)

private noncomputable def blackAtColumn
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (x : Fin 2025) :
    ↥all_black :=
  (blackXEquiv hvalid).symm x

private lemma blackAtColumn_mem
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (x : Fin 2025) :
    (blackAtColumn hvalid x).1 ∈ all_black :=
  (blackAtColumn hvalid x).2

private lemma blackAtColumn_x
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (x : Fin 2025) :
    (blackAtColumn hvalid x).1.1 = x := by
  exact (blackXEquiv hvalid).apply_symm_apply x

private lemma blackAtColumn_unique
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (x : Fin 2025) (p : Point 2025) (hp : p ∈ all_black) (hpx : p.1 = x) :
    p = (blackAtColumn hvalid x).1 := by
  apply hvalid.2.1 p hp _ (blackAtColumn_mem hvalid x)
  change p.1.val = (blackAtColumn hvalid x).1.1.val
  rw [hpx, blackAtColumn_x hvalid x]

private noncomputable def blackPermutation
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (x : Fin 2025) : Fin 2025 :=
  (blackAtColumn hvalid x).1.2

private lemma blackPermutation_bijective
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Function.Bijective (blackPermutation hvalid) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro x z hxz
    have hp := hvalid.2.2.1
      (blackAtColumn hvalid x).1 (blackAtColumn_mem hvalid x)
      (blackAtColumn hvalid z).1 (blackAtColumn_mem hvalid z)
      (congrArg Fin.val hxz)
    rw [← blackAtColumn_x hvalid x, ← blackAtColumn_x hvalid z]
    exact congrArg (fun p : Point 2025 => p.1) hp
  · rfl

private noncomputable def blackPermutationEquiv
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Fin 2025 ≃ Fin 2025 :=
  Equiv.ofBijective (blackPermutation hvalid) (blackPermutation_bijective hvalid)

private lemma blackPermutation_point
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (x : Fin 2025) :
    (x, blackPermutation hvalid x) ∈ all_black := by
  have hp := blackAtColumn_mem hvalid x
  convert hp using 1
  apply Prod.ext
  · exact (blackAtColumn_x hvalid x).symm
  · rfl

private lemma blackPermutationEquiv_point
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (x : Fin 2025) :
    (x, blackPermutationEquiv hvalid x) ∈ all_black := by
  simpa [blackPermutationEquiv] using blackPermutation_point hvalid x

private lemma blackPermutationEquiv_symm_point
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (y : Fin 2025) :
    ((blackPermutationEquiv hvalid).symm y, y) ∈ all_black := by
  have hp := blackPermutationEquiv_point hvalid ((blackPermutationEquiv hvalid).symm y)
  rwa [(blackPermutationEquiv hvalid).apply_symm_apply y] at hp

private lemma configurationOwner_black_ne
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    {p q : Point 2025} (hp : p ∈ all_black) (hpq : p ≠ q) :
    configurationOwner all_black partition hvalid p ≠
      configurationOwner all_black partition hvalid q := by
  intro hown
  have hq : q = p := by
    apply (configurationOwner_left_iff hvalid q ⟨p, hp⟩).1
    rw [← hown]
    exact configurationOwner_of_black hvalid hp
  exact hpq hq.symm

/-! ### Unit seams, maximal-run starts, and four-way crossings -/

private def horizontalLower (s : Fin 2025 × Fin 2024) : Point 2025 :=
  (s.1, ⟨s.2.val, by omega⟩)

private def horizontalUpper (s : Fin 2025 × Fin 2024) : Point 2025 :=
  (s.1, ⟨s.2.val + 1, by omega⟩)

private def verticalLeft (s : Fin 2024 × Fin 2025) : Point 2025 :=
  (⟨s.1.val, by omega⟩, s.2)

private def verticalRight (s : Fin 2024 × Fin 2025) : Point 2025 :=
  (⟨s.1.val + 1, by omega⟩, s.2)

private def IsHorizontalSeam {α : Type} (owner : Point 2025 → α)
    (s : Fin 2025 × Fin 2024) : Prop :=
  owner (horizontalLower s) ≠ owner (horizontalUpper s)

private def IsVerticalSeam {α : Type} (owner : Point 2025 → α)
    (s : Fin 2024 × Fin 2025) : Prop :=
  owner (verticalLeft s) ≠ owner (verticalRight s)

private noncomputable def horizontalSeams {α : Type}
    (owner : Point 2025 → α) : Finset (Fin 2025 × Fin 2024) := by
  classical
  exact Finset.univ.filter (IsHorizontalSeam owner)

private noncomputable def verticalSeams {α : Type}
    (owner : Point 2025 → α) : Finset (Fin 2024 × Fin 2025) := by
  classical
  exact Finset.univ.filter (IsVerticalSeam owner)

private def IsHorizontalRunStart {α : Type} (owner : Point 2025 → α)
    (s : Fin 2025 × Fin 2024) : Prop :=
  IsHorizontalSeam owner s ∧
    (s.1.val = 0 ∨ ∀ t : Fin 2025 × Fin 2024,
      t.1.val + 1 = s.1.val → t.2 = s.2 → ¬ IsHorizontalSeam owner t)

private def IsVerticalRunStart {α : Type} (owner : Point 2025 → α)
    (s : Fin 2024 × Fin 2025) : Prop :=
  IsVerticalSeam owner s ∧
    (s.2.val = 0 ∨ ∀ t : Fin 2024 × Fin 2025,
      t.1 = s.1 → t.2.val + 1 = s.2.val → ¬ IsVerticalSeam owner t)

private noncomputable def horizontalRunStarts {α : Type}
    (owner : Point 2025 → α) : Finset (Fin 2025 × Fin 2024) := by
  classical
  exact Finset.univ.filter (IsHorizontalRunStart owner)

private noncomputable def verticalRunStarts {α : Type}
    (owner : Point 2025 → α) : Finset (Fin 2024 × Fin 2025) := by
  classical
  exact Finset.univ.filter (IsVerticalRunStart owner)

private def crossHorizontalLeft (c : Fin 2024 × Fin 2024) : Fin 2025 × Fin 2024 :=
  (⟨c.1.val, by omega⟩, c.2)

private def crossHorizontalRight (c : Fin 2024 × Fin 2024) : Fin 2025 × Fin 2024 :=
  (⟨c.1.val + 1, by omega⟩, c.2)

private def crossVerticalLower (c : Fin 2024 × Fin 2024) : Fin 2024 × Fin 2025 :=
  (c.1, ⟨c.2.val, by omega⟩)

private def crossVerticalUpper (c : Fin 2024 × Fin 2024) : Fin 2024 × Fin 2025 :=
  (c.1, ⟨c.2.val + 1, by omega⟩)

private def IsFourWayCrossing {α : Type} (owner : Point 2025 → α)
    (c : Fin 2024 × Fin 2024) : Prop :=
  IsHorizontalSeam owner (crossHorizontalLeft c) ∧
  IsHorizontalSeam owner (crossHorizontalRight c) ∧
  IsVerticalSeam owner (crossVerticalLower c) ∧
  IsVerticalSeam owner (crossVerticalUpper c)

private noncomputable def fourWayCrossings {α : Type}
    (owner : Point 2025 → α) : Finset (Fin 2024 × Fin 2024) := by
  classical
  exact Finset.univ.filter (IsFourWayCrossing owner)

private def crossingBottomLeft (c : Fin 2024 × Fin 2024) : Point 2025 :=
  (⟨c.1.val, by omega⟩, ⟨c.2.val, by omega⟩)

private def crossingBottomRight (c : Fin 2024 × Fin 2024) : Point 2025 :=
  (⟨c.1.val + 1, by omega⟩, ⟨c.2.val, by omega⟩)

private def crossingTopLeft (c : Fin 2024 × Fin 2024) : Point 2025 :=
  (⟨c.1.val, by omega⟩, ⟨c.2.val + 1, by omega⟩)

private def crossingTopRight (c : Fin 2024 × Fin 2024) : Point 2025 :=
  (⟨c.1.val + 1, by omega⟩, ⟨c.2.val + 1, by omega⟩)

private lemma horizontalRunStart_right_iff {α : Type} (owner : Point 2025 → α)
    (c : Fin 2024 × Fin 2024) :
    IsHorizontalRunStart owner (crossHorizontalRight c) ↔
      IsHorizontalSeam owner (crossHorizontalRight c) ∧
      ¬ IsHorizontalSeam owner (crossHorizontalLeft c) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hleft
    rcases h.2 with hzero | hprev
    · simp [crossHorizontalRight] at hzero
    · exact hprev (crossHorizontalLeft c)
        (by simp [crossHorizontalLeft, crossHorizontalRight]) rfl hleft
  · rintro ⟨hright, hleft⟩
    refine ⟨hright, Or.inr ?_⟩
    intro t hx hy ht
    apply hleft
    have ht1 : t.1 = (crossHorizontalLeft c).1 := by
      apply Fin.ext
      simpa [crossHorizontalLeft, crossHorizontalRight] using hx
    have ht2 : t.2 = (crossHorizontalLeft c).2 := by
      simpa [crossHorizontalLeft] using hy
    rw [Prod.ext ht1 ht2] at ht
    exact ht

private lemma verticalRunStart_upper_iff {α : Type} (owner : Point 2025 → α)
    (c : Fin 2024 × Fin 2024) :
    IsVerticalRunStart owner (crossVerticalUpper c) ↔
      IsVerticalSeam owner (crossVerticalUpper c) ∧
      ¬ IsVerticalSeam owner (crossVerticalLower c) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hlower
    rcases h.2 with hzero | hprev
    · simp [crossVerticalUpper] at hzero
    · exact hprev (crossVerticalLower c) rfl
        (by simp [crossVerticalLower, crossVerticalUpper]) hlower
  · rintro ⟨hupper, hlower⟩
    refine ⟨hupper, Or.inr ?_⟩
    intro t hx hy ht
    apply hlower
    have ht1 : t.1 = (crossVerticalLower c).1 := by
      simpa [crossVerticalLower] using hx
    have ht2 : t.2 = (crossVerticalLower c).2 := by
      apply Fin.ext
      simpa [crossVerticalLower, crossVerticalUpper] using hy
    rw [Prod.ext ht1 ht2] at ht
    exact ht

private lemma horizontal_start_forces_upper_vertical {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner)
    (c : Fin 2024 × Fin 2024)
    (hright : IsHorizontalSeam owner (crossHorizontalRight c))
    (hnleft : ¬ IsHorizontalSeam owner (crossHorizontalLeft c)) :
    IsVerticalSeam owner (crossVerticalUpper c) := by
  intro hnupper
  have hleft : owner (crossingBottomLeft c) = owner (crossingTopLeft c) := by
    exact not_ne_iff.1 hnleft
  have hupper : owner (crossingTopLeft c) = owner (crossingTopRight c) := by
    simpa [IsVerticalSeam, crossVerticalUpper, verticalLeft, verticalRight,
      crossingTopLeft, crossingTopRight] using hnupper
  have hdiag : owner (crossingBottomLeft c) = owner (crossingTopRight c) :=
    hleft.trans hupper
  have hrect := (hclosure (crossingBottomLeft c) (crossingTopRight c) hdiag).2
  apply hright
  change owner (crossingBottomRight c) = owner (crossingTopRight c)
  have hbottomRight : owner (crossingBottomRight c) = owner (crossingBottomLeft c) := by
    simpa [crossingBottomLeft, crossingBottomRight, crossingTopRight] using hrect
  exact hbottomRight.trans hdiag

private lemma vertical_start_forces_right_horizontal {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner)
    (c : Fin 2024 × Fin 2024)
    (hupper : IsVerticalSeam owner (crossVerticalUpper c))
    (hnlower : ¬ IsVerticalSeam owner (crossVerticalLower c)) :
    IsHorizontalSeam owner (crossHorizontalRight c) := by
  intro hnright
  have hlower : owner (crossingBottomLeft c) = owner (crossingBottomRight c) := by
    exact not_ne_iff.1 hnlower
  have hright : owner (crossingBottomRight c) = owner (crossingTopRight c) := by
    simpa [IsHorizontalSeam, crossHorizontalRight, horizontalLower, horizontalUpper,
      crossingBottomRight, crossingTopRight] using hnright
  have hdiag : owner (crossingBottomLeft c) = owner (crossingTopRight c) :=
    hlower.trans hright
  have hrect := (hclosure (crossingBottomLeft c) (crossingTopRight c) hdiag).1
  apply hupper
  change owner (crossingTopLeft c) = owner (crossingTopRight c)
  have htopLeft : owner (crossingTopLeft c) = owner (crossingBottomLeft c) := by
    simpa [crossingBottomLeft, crossingTopLeft, crossingTopRight] using hrect
  exact htopLeft.trans hdiag

private lemma topLeft_interior_iff {α : Type} (owner : Point 2025 → α)
    (c : Fin 2024 × Fin 2024) :
    IsOwnerTopLeft owner (crossingTopRight c) ↔
      IsVerticalSeam owner (crossVerticalUpper c) ∧
      IsHorizontalSeam owner (crossHorizontalRight c) := by
  constructor
  · intro h
    constructor
    · apply h.1 (crossingTopLeft c)
      · simp [crossingTopLeft, crossingTopRight]
      · simp [crossingTopLeft, crossingTopRight]
    · apply h.2 (crossingBottomRight c)
      · simp [crossingBottomRight, crossingTopRight]
      · simp [crossingBottomRight, crossingTopRight]
  · rintro ⟨hupper, hright⟩
    constructor
    · intro q hx hy
      have hqx : px q = c.1.val := by
        change px q + 1 = c.1.val + 1 at hx
        omega
      have hqy : py q = c.2.val + 1 := by
        change py q = c.2.val + 1 at hy
        exact hy
      have hq : q = crossingTopLeft c := by
        apply Prod.ext
        · apply Fin.ext
          simpa [crossingTopLeft] using hqx
        · apply Fin.ext
          simpa [crossingTopLeft] using hqy
      subst q
      exact hupper
    · intro q hx hy
      have hqx : px q = c.1.val + 1 := by
        change px q = c.1.val + 1 at hx
        exact hx
      have hqy : py q = c.2.val := by
        change py q + 1 = c.2.val + 1 at hy
        omega
      have hq : q = crossingBottomRight c := by
        apply Prod.ext
        · apply Fin.ext
          simpa [crossingBottomRight] using hqx
        · apply Fin.ext
          simpa [crossingBottomRight] using hqy
      subst q
      exact hright

/-- This is the finite local rectangle-closure classification used at every
interior lattice vertex in the seam identity. -/
private lemma interior_topLeft_classification {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner)
    (c : Fin 2024 × Fin 2024) :
    IsOwnerTopLeft owner (crossingTopRight c) ↔
      IsHorizontalRunStart owner (crossHorizontalRight c) ∨
      IsVerticalRunStart owner (crossVerticalUpper c) ∨
      IsFourWayCrossing owner c := by
  rw [topLeft_interior_iff owner c,
    horizontalRunStart_right_iff owner c, verticalRunStart_upper_iff owner c]
  constructor
  · rintro ⟨hupper, hright⟩
    by_cases hleft : IsHorizontalSeam owner (crossHorizontalLeft c)
    · by_cases hlower : IsVerticalSeam owner (crossVerticalLower c)
      · exact Or.inr (Or.inr ⟨hleft, hright, hlower, hupper⟩)
      · exact Or.inr (Or.inl ⟨hupper, hlower⟩)
    · exact Or.inl ⟨hright, hleft⟩
  · rintro (hstart | vstart | hcross)
    · exact ⟨horizontal_start_forces_upper_vertical owner hclosure c hstart.1 hstart.2,
        hstart.1⟩
    · exact ⟨vstart.1,
        vertical_start_forces_right_horizontal owner hclosure c vstart.1 vstart.2⟩
    · exact ⟨hcross.2.2.2, hcross.2.1⟩

private def ownerOrigin : Point 2025 := (0, 0)

private def horizontalStartPoint (s : Fin 2025 × Fin 2024) : Point 2025 :=
  horizontalUpper s

private def verticalStartPoint (s : Fin 2024 × Fin 2025) : Point 2025 :=
  verticalRight s

private lemma ownerOrigin_isTopLeft {α : Type} (owner : Point 2025 → α) :
    IsOwnerTopLeft owner ownerOrigin := by
  constructor
  · intro q hx
    simp [ownerOrigin] at hx
  · intro q hx hy
    simp [ownerOrigin] at hy

private lemma horizontalRunStart_isTopLeft {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner)
    (s : Fin 2025 × Fin 2024) (hs : IsHorizontalRunStart owner s) :
    IsOwnerTopLeft owner (horizontalStartPoint s) := by
  by_cases hx0 : s.1.val = 0
  · constructor
    · intro q hx
      change px q + 1 = s.1.val at hx
      omega
    · intro q hx hy
      have hq : q = horizontalLower s := by
        apply Prod.ext
        · apply Fin.ext
          change px q = s.1.val at hx
          simpa [horizontalLower] using hx
        · apply Fin.ext
          change py q + 1 = s.2.val + 1 at hy
          change py q = s.2.val
          omega
      subst q
      exact hs.1
  · have hxpos : 0 < s.1.val := Nat.pos_of_ne_zero hx0
    let c : Fin 2024 × Fin 2024 :=
      (⟨s.1.val - 1, by omega⟩, s.2)
    have hsc : s = crossHorizontalRight c := by
      apply Prod.ext
      · apply Fin.ext
        dsimp [c, crossHorizontalRight]
        omega
      · rfl
    have hpc : horizontalStartPoint s = crossingTopRight c := by
      rw [hsc]
      apply Prod.ext <;> apply Fin.ext <;>
        simp [horizontalStartPoint, horizontalUpper, crossHorizontalRight,
          crossingTopRight, c]
    rw [hpc]
    apply (interior_topLeft_classification owner hclosure c).2
    exact Or.inl (hsc ▸ hs)

private lemma verticalRunStart_isTopLeft {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner)
    (s : Fin 2024 × Fin 2025) (hs : IsVerticalRunStart owner s) :
    IsOwnerTopLeft owner (verticalStartPoint s) := by
  by_cases hy0 : s.2.val = 0
  · constructor
    · intro q hx hy
      have hq : q = verticalLeft s := by
        apply Prod.ext
        · apply Fin.ext
          change px q + 1 = s.1.val + 1 at hx
          change px q = s.1.val
          omega
        · apply Fin.ext
          change py q = s.2.val at hy
          simpa [verticalLeft] using hy
      subst q
      exact hs.1
    · intro q hx hy
      change py q + 1 = s.2.val at hy
      omega
  · have hypos : 0 < s.2.val := Nat.pos_of_ne_zero hy0
    let c : Fin 2024 × Fin 2024 :=
      (s.1, ⟨s.2.val - 1, by omega⟩)
    have hsc : s = crossVerticalUpper c := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        dsimp [c, crossVerticalUpper]
        omega
    have hpc : verticalStartPoint s = crossingTopRight c := by
      rw [hsc]
      apply Prod.ext <;> apply Fin.ext <;>
        simp [verticalStartPoint, verticalRight, crossVerticalUpper,
          crossingTopRight, c]
    rw [hpc]
    apply (interior_topLeft_classification owner hclosure c).2
    exact Or.inr (Or.inl (hsc ▸ hs))

private lemma crossing_isTopLeft {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner)
    (c : Fin 2024 × Fin 2024) (hc : IsFourWayCrossing owner c) :
    IsOwnerTopLeft owner (crossingTopRight c) := by
  exact (interior_topLeft_classification owner hclosure c).2 (Or.inr (Or.inr hc))

private lemma horizontal_vertical_starts_disjoint {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner)
    (c : Fin 2024 × Fin 2024)
    (hh : IsHorizontalRunStart owner (crossHorizontalRight c))
    (hv : IsVerticalRunStart owner (crossVerticalUpper c)) : False := by
  have hnleft : ¬ IsHorizontalSeam owner (crossHorizontalLeft c) :=
    (horizontalRunStart_right_iff owner c).1 hh |>.2
  have hnlower : ¬ IsVerticalSeam owner (crossVerticalLower c) :=
    (verticalRunStart_upper_iff owner c).1 hv |>.2
  have hleft : owner (crossingBottomLeft c) = owner (crossingTopLeft c) := by
    simpa [IsHorizontalSeam, crossHorizontalLeft, horizontalLower, horizontalUpper,
      crossingBottomLeft, crossingTopLeft] using hnleft
  have hlower : owner (crossingBottomLeft c) = owner (crossingBottomRight c) := by
    simpa [IsVerticalSeam, crossVerticalLower, verticalLeft, verticalRight,
      crossingBottomLeft, crossingBottomRight] using hnlower
  have hdiag : owner (crossingTopLeft c) = owner (crossingBottomRight c) :=
    hleft.symm.trans hlower
  have hrect := (hclosure (crossingTopLeft c) (crossingBottomRight c) hdiag).2
  have hright : IsHorizontalSeam owner (crossHorizontalRight c) := hh.1
  apply hright
  have htopRight : owner (crossingTopRight c) = owner (crossingTopLeft c) := by
    simpa [crossingTopLeft, crossingBottomRight, crossingTopRight] using hrect
  have heq : owner (crossingBottomRight c) = owner (crossingTopRight c) :=
    hlower.symm.trans (hleft.trans htopRight.symm)
  simpa [IsHorizontalSeam, crossHorizontalRight, horizontalLower, horizontalUpper,
    crossingBottomRight, crossingTopRight] using heq

private noncomputable def classifiedTopLefts {α : Type}
    (owner : Point 2025 → α) : Finset (Point 2025) := by
  classical
  exact (({ownerOrigin} ∪
    (horizontalRunStarts owner).image horizontalStartPoint) ∪
    (verticalRunStarts owner).image verticalStartPoint) ∪
    (fourWayCrossings owner).image crossingTopRight

private lemma topLeft_mem_classified {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner)
    (p : Point 2025) (hp : IsOwnerTopLeft owner p) :
    p ∈ classifiedTopLefts owner := by
  classical
  by_cases hx0 : px p = 0
  · by_cases hy0 : py p = 0
    · have hpo : p = ownerOrigin := by
        apply Prod.ext <;> apply Fin.ext
        · simpa [ownerOrigin] using hx0
        · simpa [ownerOrigin] using hy0
      simp [classifiedTopLefts, hpo]
    · have hypos : 0 < py p := Nat.pos_of_ne_zero hy0
      have hpylt : py p < 2025 := p.2.isLt
      let s : Fin 2025 × Fin 2024 :=
        (p.1, ⟨py p - 1, by show py p - 1 < 2024; omega⟩)
      have hsy : s.2.val = py p - 1 := by rfl
      have hsp : horizontalStartPoint s = p := by
        apply Prod.ext <;> apply Fin.ext
        · rfl
        · change s.2.val + 1 = py p
          rw [hsy]
          omega
      have hs : IsHorizontalRunStart owner s := by
        constructor
        · change owner (horizontalLower s) ≠ owner (horizontalStartPoint s)
          rw [hsp]
          apply hp.2 (horizontalLower s)
          · rfl
          · change s.2.val + 1 = py p
            rw [hsy]
            omega
        · left
          simpa [s] using hx0
      have hmem : horizontalStartPoint s ∈
          (horizontalRunStarts owner).image horizontalStartPoint := by
        apply Finset.mem_image.2
        refine ⟨s, ?_, rfl⟩
        apply Finset.mem_filter.2
        exact ⟨Finset.mem_univ _, hs⟩
      rw [← hsp]
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ hmem))
  · have hxpos : 0 < px p := Nat.pos_of_ne_zero hx0
    have hpxlt : px p < 2025 := p.1.isLt
    by_cases hy0 : py p = 0
    · let s : Fin 2024 × Fin 2025 :=
        (⟨px p - 1, by show px p - 1 < 2024; omega⟩, p.2)
      have hsx : s.1.val = px p - 1 := by rfl
      have hsp : verticalStartPoint s = p := by
        apply Prod.ext <;> apply Fin.ext
        · change s.1.val + 1 = px p
          rw [hsx]
          omega
        · rfl
      have hs : IsVerticalRunStart owner s := by
        constructor
        · change owner (verticalLeft s) ≠ owner (verticalStartPoint s)
          rw [hsp]
          apply hp.1 (verticalLeft s)
          · change s.1.val + 1 = px p
            rw [hsx]
            omega
          · rfl
        · left
          simpa [s] using hy0
      have hmem : verticalStartPoint s ∈
          (verticalRunStarts owner).image verticalStartPoint := by
        apply Finset.mem_image.2
        refine ⟨s, ?_, rfl⟩
        apply Finset.mem_filter.2
        exact ⟨Finset.mem_univ _, hs⟩
      rw [← hsp]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hmem)
    · have hypos : 0 < py p := Nat.pos_of_ne_zero hy0
      have hpylt : py p < 2025 := p.2.isLt
      let c : Fin 2024 × Fin 2024 :=
        (⟨px p - 1, by show px p - 1 < 2024; omega⟩,
         ⟨py p - 1, by show py p - 1 < 2024; omega⟩)
      have hcx : c.1.val = px p - 1 := by rfl
      have hcy : c.2.val = py p - 1 := by rfl
      have hpc : crossingTopRight c = p := by
        apply Prod.ext <;> apply Fin.ext
        · change c.1.val + 1 = px p
          rw [hcx]
          omega
        · change c.2.val + 1 = py p
          rw [hcy]
          omega
      have hclass := (interior_topLeft_classification owner hclosure c).1
        (hpc ▸ hp)
      rcases hclass with hh | hv | hc
      · have hmem : horizontalStartPoint (crossHorizontalRight c) ∈
            (horizontalRunStarts owner).image horizontalStartPoint := by
          apply Finset.mem_image.2
          refine ⟨crossHorizontalRight c, ?_, rfl⟩
          apply Finset.mem_filter.2
          exact ⟨Finset.mem_univ _, hh⟩
        have heq : horizontalStartPoint (crossHorizontalRight c) = p := by
          rw [← hpc]
          apply Prod.ext <;> apply Fin.ext <;>
            simp [horizontalStartPoint, horizontalUpper, crossHorizontalRight,
              crossingTopRight]
        rw [← heq]
        exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ hmem))
      · have hmem : verticalStartPoint (crossVerticalUpper c) ∈
            (verticalRunStarts owner).image verticalStartPoint := by
          apply Finset.mem_image.2
          refine ⟨crossVerticalUpper c, ?_, rfl⟩
          apply Finset.mem_filter.2
          exact ⟨Finset.mem_univ _, hv⟩
        have heq : verticalStartPoint (crossVerticalUpper c) = p := by
          rw [← hpc]
          apply Prod.ext <;> apply Fin.ext <;>
            simp [verticalStartPoint, verticalRight, crossVerticalUpper,
              crossingTopRight]
        rw [← heq]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hmem)
      · have hmem : crossingTopRight c ∈
            (fourWayCrossings owner).image crossingTopRight := by
          apply Finset.mem_image.2
          refine ⟨c, ?_, rfl⟩
          apply Finset.mem_filter.2
          exact ⟨Finset.mem_univ _, hc⟩
        rw [← hpc]
        exact Finset.mem_union_right _ hmem

private lemma classified_mem_topLeft {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner)
    (p : Point 2025) (hp : p ∈ classifiedTopLefts owner) :
    IsOwnerTopLeft owner p := by
  classical
  change p ∈ ((({ownerOrigin} ∪
    (horizontalRunStarts owner).image horizontalStartPoint) ∪
    (verticalRunStarts owner).image verticalStartPoint) ∪
    (fourWayCrossings owner).image crossingTopRight) at hp
  rcases Finset.mem_union.1 hp with hpOHV | hpC
  · rcases Finset.mem_union.1 hpOHV with hpOH | hpV
    · rcases Finset.mem_union.1 hpOH with hpO | hpH
      · have hpEq : p = ownerOrigin := Finset.mem_singleton.1 hpO
        subst p
        exact ownerOrigin_isTopLeft owner
      · obtain ⟨s, hs, hsp⟩ := Finset.mem_image.1 hpH
        rw [← hsp]
        exact horizontalRunStart_isTopLeft owner hclosure s (Finset.mem_filter.1 hs).2
    · obtain ⟨s, hs, hsp⟩ := Finset.mem_image.1 hpV
      rw [← hsp]
      exact verticalRunStart_isTopLeft owner hclosure s (Finset.mem_filter.1 hs).2
  · obtain ⟨c, hc, hcp⟩ := Finset.mem_image.1 hpC
    rw [← hcp]
    exact crossing_isTopLeft owner hclosure c (Finset.mem_filter.1 hc).2

private lemma ownerTopLefts_eq_classified
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    ownerTopLefts hvalid = classifiedTopLefts
      (configurationOwner all_black partition hvalid) := by
  classical
  ext p
  change (p ∈ Finset.univ.filter
      (IsOwnerTopLeft (configurationOwner all_black partition hvalid))) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact ⟨topLeft_mem_classified _ (configurationOwner_hasRectangleClosure hvalid) p,
    classified_mem_topLeft _ (configurationOwner_hasRectangleClosure hvalid) p⟩

private lemma horizontalStartPoint_injective :
    Function.Injective horizontalStartPoint := by
  intro s t h
  apply Prod.ext
  · have hx := congrArg (fun p : Point 2025 => p.1) h
    change s.1 = t.1
    simpa [horizontalStartPoint, horizontalUpper] using hx
  · apply Fin.ext
    have hy := congrArg (fun p : Point 2025 => py p) h
    change s.2.val + 1 = t.2.val + 1 at hy
    omega

private lemma verticalStartPoint_injective :
    Function.Injective verticalStartPoint := by
  intro s t h
  apply Prod.ext
  · apply Fin.ext
    have hx := congrArg (fun p : Point 2025 => px p) h
    change s.1.val + 1 = t.1.val + 1 at hx
    omega
  · have hy := congrArg (fun p : Point 2025 => p.2) h
    change s.2 = t.2
    simpa [verticalStartPoint, verticalRight] using hy

private lemma crossingTopRight_injective :
    Function.Injective crossingTopRight := by
  intro c d h
  apply Prod.ext <;> apply Fin.ext
  · have hx := congrArg (fun p : Point 2025 => px p) h
    change c.1.val + 1 = d.1.val + 1 at hx
    omega
  · have hy := congrArg (fun p : Point 2025 => py p) h
    change c.2.val + 1 = d.2.val + 1 at hy
    omega

private lemma ownerOrigin_not_horizontalStartPoint
    (s : Fin 2025 × Fin 2024) : ownerOrigin ≠ horizontalStartPoint s := by
  intro h
  have hy := congrArg (fun p : Point 2025 => py p) h
  simp [ownerOrigin, horizontalStartPoint, horizontalUpper] at hy

private lemma ownerOrigin_not_verticalStartPoint
    (s : Fin 2024 × Fin 2025) : ownerOrigin ≠ verticalStartPoint s := by
  intro h
  have hx := congrArg (fun p : Point 2025 => px p) h
  simp [ownerOrigin, verticalStartPoint, verticalRight] at hx

private lemma ownerOrigin_not_crossingTopRight
    (c : Fin 2024 × Fin 2024) : ownerOrigin ≠ crossingTopRight c := by
  intro h
  have hx := congrArg (fun p : Point 2025 => px p) h
  simp [ownerOrigin, crossingTopRight] at hx

private lemma horizontalStartPoint_ne_verticalStartPoint {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner)
    (s : Fin 2025 × Fin 2024) (hs : IsHorizontalRunStart owner s)
    (t : Fin 2024 × Fin 2025) (ht : IsVerticalRunStart owner t) :
    horizontalStartPoint s ≠ verticalStartPoint t := by
  intro hst
  have hx : s.1.val = t.1.val + 1 := by
    have := congrArg (fun p : Point 2025 => px p) hst
    simpa [horizontalStartPoint, horizontalUpper, verticalStartPoint, verticalRight] using this
  have hy : s.2.val + 1 = t.2.val := by
    have := congrArg (fun p : Point 2025 => py p) hst
    simpa [horizontalStartPoint, horizontalUpper, verticalStartPoint, verticalRight] using this
  let c : Fin 2024 × Fin 2024 := (t.1, s.2)
  have hs' : s = crossHorizontalRight c := by
    apply Prod.ext
    · apply Fin.ext
      simpa [c, crossHorizontalRight] using hx
    · rfl
  have ht' : t = crossVerticalUpper c := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simpa [c, crossVerticalUpper] using hy.symm
  exact horizontal_vertical_starts_disjoint owner hclosure c (hs' ▸ hs) (ht' ▸ ht)

private lemma horizontalStartPoint_ne_crossingTopRight {α : Type}
    (owner : Point 2025 → α)
    (s : Fin 2025 × Fin 2024) (hs : IsHorizontalRunStart owner s)
    (c : Fin 2024 × Fin 2024) (hc : IsFourWayCrossing owner c) :
    horizontalStartPoint s ≠ crossingTopRight c := by
  intro h
  have hx : s.1.val = c.1.val + 1 := by
    have := congrArg (fun p : Point 2025 => px p) h
    simpa [horizontalStartPoint, horizontalUpper, crossingTopRight] using this
  have hy : s.2 = c.2 := by
    apply Fin.ext
    have hval := congrArg (fun p : Point 2025 => py p) h
    change s.2.val + 1 = c.2.val + 1 at hval
    omega
  have hs' : s = crossHorizontalRight c := by
    apply Prod.ext
    · apply Fin.ext
      simpa [crossHorizontalRight] using hx
    · exact hy
  have hnleft := (horizontalRunStart_right_iff owner c).1 (hs' ▸ hs) |>.2
  exact hnleft hc.1

private lemma verticalStartPoint_ne_crossingTopRight {α : Type}
    (owner : Point 2025 → α)
    (s : Fin 2024 × Fin 2025) (hs : IsVerticalRunStart owner s)
    (c : Fin 2024 × Fin 2024) (hc : IsFourWayCrossing owner c) :
    verticalStartPoint s ≠ crossingTopRight c := by
  intro h
  have hx : s.1 = c.1 := by
    apply Fin.ext
    have hval := congrArg (fun p : Point 2025 => px p) h
    change s.1.val + 1 = c.1.val + 1 at hval
    omega
  have hy : s.2.val = c.2.val + 1 := by
    have := congrArg (fun p : Point 2025 => py p) h
    simpa [verticalStartPoint, verticalRight, crossingTopRight] using this
  have hs' : s = crossVerticalUpper c := by
    apply Prod.ext
    · exact hx
    · apply Fin.ext
      simpa [crossVerticalUpper] using hy
  have hnlower := (verticalRunStart_upper_iff owner c).1 (hs' ▸ hs) |>.2
  exact hnlower hc.2.2.1

private lemma classifiedTopLefts_card {α : Type}
    (owner : Point 2025 → α) (hclosure : HasRectangleClosure owner) :
    (classifiedTopLefts owner).card =
      1 + (horizontalRunStarts owner).card +
        (verticalRunStarts owner).card + (fourWayCrossings owner).card := by
  classical
  let H := (horizontalRunStarts owner).image horizontalStartPoint
  let V := (verticalRunStarts owner).image verticalStartPoint
  let C := (fourWayCrossings owner).image crossingTopRight
  have hH : H.card = (horizontalRunStarts owner).card := by
    exact Finset.card_image_of_injective _ horizontalStartPoint_injective
  have hV : V.card = (verticalRunStarts owner).card := by
    exact Finset.card_image_of_injective _ verticalStartPoint_injective
  have hC : C.card = (fourWayCrossings owner).card := by
    exact Finset.card_image_of_injective _ crossingTopRight_injective
  have hOH : Disjoint {ownerOrigin} H := by
    rw [Finset.disjoint_left]
    intro p hpO hpH
    have hp : p = ownerOrigin := Finset.mem_singleton.1 hpO
    obtain ⟨s, hs, hsp⟩ := Finset.mem_image.1 hpH
    exact ownerOrigin_not_horizontalStartPoint s (hp.symm.trans hsp.symm)
  have hOV : Disjoint {ownerOrigin} V := by
    rw [Finset.disjoint_left]
    intro p hpO hpV
    have hp : p = ownerOrigin := Finset.mem_singleton.1 hpO
    obtain ⟨s, hs, hsp⟩ := Finset.mem_image.1 hpV
    exact ownerOrigin_not_verticalStartPoint s (hp.symm.trans hsp.symm)
  have hOC : Disjoint {ownerOrigin} C := by
    rw [Finset.disjoint_left]
    intro p hpO hpC
    have hp : p = ownerOrigin := Finset.mem_singleton.1 hpO
    obtain ⟨c, hc, hcp⟩ := Finset.mem_image.1 hpC
    exact ownerOrigin_not_crossingTopRight c (hp.symm.trans hcp.symm)
  have hHV : Disjoint H V := by
    rw [Finset.disjoint_left]
    intro p hpH hpV
    obtain ⟨s, hs, hsp⟩ := Finset.mem_image.1 hpH
    obtain ⟨t, ht, htp⟩ := Finset.mem_image.1 hpV
    apply horizontalStartPoint_ne_verticalStartPoint owner hclosure s
      (Finset.mem_filter.1 hs).2 t (Finset.mem_filter.1 ht).2
    exact hsp.trans htp.symm
  have hHC : Disjoint H C := by
    rw [Finset.disjoint_left]
    intro p hpH hpC
    obtain ⟨s, hs, hsp⟩ := Finset.mem_image.1 hpH
    obtain ⟨c, hc, hcp⟩ := Finset.mem_image.1 hpC
    apply horizontalStartPoint_ne_crossingTopRight owner s
      (Finset.mem_filter.1 hs).2 c (Finset.mem_filter.1 hc).2
    exact hsp.trans hcp.symm
  have hVC : Disjoint V C := by
    rw [Finset.disjoint_left]
    intro p hpV hpC
    obtain ⟨s, hs, hsp⟩ := Finset.mem_image.1 hpV
    obtain ⟨c, hc, hcp⟩ := Finset.mem_image.1 hpC
    apply verticalStartPoint_ne_crossingTopRight owner s
      (Finset.mem_filter.1 hs).2 c (Finset.mem_filter.1 hc).2
    exact hsp.trans hcp.symm
  change ((({ownerOrigin} ∪ H) ∪ V) ∪ C).card = _
  rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hOC, hHC⟩, hVC⟩),
    Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hOV, hHV⟩),
    Finset.card_union_of_disjoint hOH, hH, hV, hC]
  simp

private lemma configuration_seam_identity
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    partition.card + 2025 =
      1 + (horizontalRunStarts
        (configurationOwner all_black partition hvalid)).card +
        (verticalRunStarts
          (configurationOwner all_black partition hvalid)).card +
        (fourWayCrossings
          (configurationOwner all_black partition hvalid)).card := by
  have howners : (ownerTopLefts hvalid).card = 2025 + partition.card := by
    simpa [hvalid.1] using ownerTopLefts_card hvalid
  have hclassified : (classifiedTopLefts
      (configurationOwner all_black partition hvalid)).card =
      1 + (horizontalRunStarts
        (configurationOwner all_black partition hvalid)).card +
        (verticalRunStarts
          (configurationOwner all_black partition hvalid)).card +
        (fourWayCrossings
          (configurationOwner all_black partition hvalid)).card :=
    classifiedTopLefts_card _ (configurationOwner_hasRectangleClosure hvalid)
  rw [ownerTopLefts_eq_classified hvalid] at howners
  omega

/-! ### Adjacent-row and adjacent-column tangents -/

private def gapLower (g : Fin 2024) : Fin 2025 := ⟨g.val, by omega⟩
private def gapUpper (g : Fin 2024) : Fin 2025 := ⟨g.val + 1, by omega⟩

private def rowTangentStart (σ : Fin 2025 ≃ Fin 2025) (g : Fin 2024) : ℕ :=
  min (σ.symm (gapLower g)).val (σ.symm (gapUpper g)).val + 1

private def rowTangentStop (σ : Fin 2025 ≃ Fin 2025) (g : Fin 2024) : ℕ :=
  max (σ.symm (gapLower g)).val (σ.symm (gapUpper g)).val

private def columnTangentStart (σ : Fin 2025 ≃ Fin 2025) (g : Fin 2024) : ℕ :=
  min (σ (gapLower g)).val (σ (gapUpper g)).val + 1

private def columnTangentStop (σ : Fin 2025 ≃ Fin 2025) (g : Fin 2024) : ℕ :=
  max (σ (gapLower g)).val (σ (gapUpper g)).val

private lemma gapLower_ne_gapUpper (g : Fin 2024) : gapLower g ≠ gapUpper g := by
  intro h
  have := congrArg Fin.val h
  simp [gapLower, gapUpper] at this

private lemma rowTangentStart_le_stop (σ : Fin 2025 ≃ Fin 2025) (g : Fin 2024) :
    rowTangentStart σ g ≤ rowTangentStop σ g := by
  have hne : σ.symm (gapLower g) ≠ σ.symm (gapUpper g) :=
    σ.symm.injective.ne (gapLower_ne_gapUpper g)
  have hval : (σ.symm (gapLower g)).val ≠ (σ.symm (gapUpper g)).val := by
    exact fun h => hne (Fin.ext h)
  simp only [rowTangentStart, rowTangentStop]
  omega

private lemma columnTangentStart_le_stop (σ : Fin 2025 ≃ Fin 2025) (g : Fin 2024) :
    columnTangentStart σ g ≤ columnTangentStop σ g := by
  have hne : σ (gapLower g) ≠ σ (gapUpper g) :=
    σ.injective.ne (gapLower_ne_gapUpper g)
  have hval : (σ (gapLower g)).val ≠ (σ (gapUpper g)).val := by
    exact fun h => hne (Fin.ext h)
  simp only [columnTangentStart, columnTangentStop]
  omega

private def IsRowTangentSupported {α : Type} (owner : Point 2025 → α)
    (σ : Fin 2025 ≃ Fin 2025) (g : Fin 2024) : Prop :=
  ∀ x : Fin 2025, rowTangentStart σ g - 1 ≤ x.val → x.val ≤ rowTangentStop σ g →
    IsHorizontalSeam owner (x, g)

private def IsColumnTangentSupported {α : Type} (owner : Point 2025 → α)
    (σ : Fin 2025 ≃ Fin 2025) (g : Fin 2024) : Prop :=
  ∀ y : Fin 2025, columnTangentStart σ g - 1 ≤ y.val → y.val ≤ columnTangentStop σ g →
    IsVerticalSeam owner (g, y)

private noncomputable def supportedRowTangents {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025) : Finset (Fin 2024) := by
  classical
  exact Finset.univ.filter (IsRowTangentSupported owner σ)

private noncomputable def supportedColumnTangents {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025) : Finset (Fin 2024) := by
  classical
  exact Finset.univ.filter (IsColumnTangentSupported owner σ)

/-- Tangent grid lines use the standard half-open cut convention.  Support
includes every endpoint seam unit, so a diagonal tangent is nonvacuous. -/
private def TangentConflict (σ : Fin 2025 ≃ Fin 2025)
    (h v : Fin 2024) : Prop :=
  rowTangentStart σ h - 1 ≤ v.val ∧ v.val < rowTangentStop σ h ∧
  columnTangentStart σ v - 1 ≤ h.val ∧ h.val < columnTangentStop σ v

private lemma supported_tangent_conflict_is_crossing {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025)
    (h v : Fin 2024) (hh : IsRowTangentSupported owner σ h)
    (hv : IsColumnTangentSupported owner σ v) (hc : TangentConflict σ h v) :
    IsFourWayCrossing owner (v, h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hh (gapLower v)
    · simpa [gapLower] using hc.1
    · simpa [gapLower] using hc.2.1.le
  · apply hh (gapUpper v)
    · simpa [gapUpper] using hc.1.trans (Nat.le_succ v.val)
    · simpa [gapUpper] using hc.2.1
  · apply hv (gapLower h)
    · simpa [gapLower] using hc.2.2.1
    · simpa [gapLower] using hc.2.2.2.le
  · apply hv (gapUpper h)
    · simpa [gapUpper] using hc.2.2.1.trans (Nat.le_succ h.val)
    · simpa [gapUpper] using hc.2.2.2

private noncomputable def tangentConflicts {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025) :
    Finset (Fin 2024 × Fin 2024) := by
  classical
  exact Finset.univ.filter (fun z =>
    IsRowTangentSupported owner σ z.1 ∧
    IsColumnTangentSupported owner σ z.2 ∧ TangentConflict σ z.1 z.2)

private lemma tangentConflicts_card_le_crossings {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025) :
    (tangentConflicts owner σ).card ≤ (fourWayCrossings owner).card := by
  classical
  let swap : Fin 2024 × Fin 2024 → Fin 2024 × Fin 2024 := fun z => (z.2, z.1)
  have hswap : Function.Injective swap := by
    intro a b h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hsub : (tangentConflicts owner σ).image swap ⊆ fourWayCrossings owner := by
    intro c hc
    obtain ⟨z, hz, hzc⟩ := Finset.mem_image.1 hc
    rw [← hzc]
    have hzs : IsRowTangentSupported owner σ z.1 := by
      exact (Finset.mem_filter.1 hz).2.1
    have hzv : IsColumnTangentSupported owner σ z.2 := by
      exact (Finset.mem_filter.1 hz).2.2.1
    have hzcfl : TangentConflict σ z.1 z.2 := by
      exact (Finset.mem_filter.1 hz).2.2.2
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_univ _,
      supported_tangent_conflict_is_crossing owner σ z.1 z.2 hzs hzv hzcfl⟩
  rw [← Finset.card_image_of_injective _ hswap]
  exact Finset.card_le_card hsub

private noncomputable def conflictingRowTangents {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025) : Finset (Fin 2024) :=
  (tangentConflicts owner σ).image Prod.fst

private noncomputable def compatibleRowTangents {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025) : Finset (Fin 2024) :=
  supportedRowTangents owner σ \ conflictingRowTangents owner σ

private noncomputable def compatibleColumnTangents {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025) : Finset (Fin 2024) :=
  supportedColumnTangents owner σ

private lemma compatible_tangents_no_conflict {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025)
    {h v : Fin 2024} (hh : h ∈ compatibleRowTangents owner σ)
    (hv : v ∈ compatibleColumnTangents owner σ) : ¬ TangentConflict σ h v := by
  classical
  intro hc
  have hhparts : h ∈ supportedRowTangents owner σ ∧
      h ∉ conflictingRowTangents owner σ := by
    exact Finset.mem_sdiff.1 hh
  have hhs : IsRowTangentSupported owner σ h := by
    exact (Finset.mem_filter.1 hhparts.1).2
  have hvs : IsColumnTangentSupported owner σ v := by
    exact (Finset.mem_filter.1 hv).2
  have hp : (h, v) ∈ tangentConflicts owner σ := by
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_univ _, hhs, hvs, hc⟩
  apply hhparts.2
  exact Finset.mem_image.2 ⟨(h, v), hp, rfl⟩

private lemma conflictingRowTangents_subset_supported {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025) :
    conflictingRowTangents owner σ ⊆ supportedRowTangents owner σ := by
  classical
  intro h hh
  obtain ⟨z, hz, hzh⟩ := Finset.mem_image.1 hh
  subst h
  simp only [tangentConflicts, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  simp only [supportedRowTangents, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hz.1

private lemma supportedRowTangents_card_le_compatible_add_conflicts {α : Type}
    (owner : Point 2025 → α) (σ : Fin 2025 ≃ Fin 2025) :
    (supportedRowTangents owner σ).card ≤
      (compatibleRowTangents owner σ).card + (tangentConflicts owner σ).card := by
  classical
  have hsub := conflictingRowTangents_subset_supported owner σ
  have hconf : (conflictingRowTangents owner σ).card ≤
      (tangentConflicts owner σ).card := by
    exact Finset.card_image_le
  rw [compatibleRowTangents, Finset.card_sdiff_of_subset hsub]
  omega

private def componentIndex (selected : Finset (Fin 2024)) (i : Fin 2025) : ℕ :=
  ((Finset.univ \ selected).filter (fun g => g.val < i.val)).card

private lemma componentIndex_le (selected : Finset (Fin 2024)) (i : Fin 2025) :
    componentIndex selected i ≤ 2024 - selected.card := by
  classical
  calc
    componentIndex selected i ≤ (Finset.univ \ selected).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2024 - selected.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ selected)]
      simp

private lemma componentIndex_lt (selected : Finset (Fin 2024)) (i : Fin 2025) :
    componentIndex selected i < 2025 - selected.card := by
  have hcard : selected.card ≤ 2024 := by simpa using selected.card_le_univ
  have hle := componentIndex_le selected i
  omega

private def componentLabel (selected : Finset (Fin 2024)) (i : Fin 2025) :
    Fin (2025 - selected.card) :=
  ⟨componentIndex selected i, componentIndex_lt selected i⟩

private lemma componentIndex_eq_of_selected_between
    (selected : Finset (Fin 2024)) (i j : Fin 2025)
    (hselected : ∀ g : Fin 2024, min i.val j.val ≤ g.val →
      g.val < max i.val j.val → g ∈ selected) :
    componentIndex selected i = componentIndex selected j := by
  classical
  apply congrArg Finset.card
  ext g
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  by_cases hij : i.val ≤ j.val
  · have hmin : min i.val j.val = i.val := min_eq_left hij
    have hmax : max i.val j.val = j.val := max_eq_right hij
    constructor
    · rintro ⟨hnot, hgi⟩
      exact ⟨hnot, lt_of_lt_of_le hgi hij⟩
    · rintro ⟨hnot, hgj⟩
      refine ⟨hnot, ?_⟩
      by_contra hgi
      exact hnot (hselected g (by omega) (by omega))
  · have hji : j.val ≤ i.val := le_of_not_ge hij
    have hmin : min i.val j.val = j.val := min_eq_right hji
    have hmax : max i.val j.val = i.val := max_eq_left hji
    constructor
    · rintro ⟨hnot, hgi⟩
      refine ⟨hnot, ?_⟩
      by_contra hgj
      exact hnot (hselected g (by omega) (by omega))
    · rintro ⟨hnot, hgj⟩
      exact ⟨hnot, lt_of_lt_of_le hgj hji⟩

private lemma componentLabel_eq_of_selected_between
    (selected : Finset (Fin 2024)) (i j : Fin 2025)
    (hselected : ∀ g : Fin 2024, min i.val j.val ≤ g.val →
      g.val < max i.val j.val → g ∈ selected) :
    componentLabel selected i = componentLabel selected j := by
  apply Fin.ext
  exact componentIndex_eq_of_selected_between selected i j hselected

private lemma selected_between_of_componentLabel_eq
    (selected : Finset (Fin 2024)) (i j : Fin 2025)
    (hlabel : componentLabel selected i = componentLabel selected j)
    (g : Fin 2024) (hlo : min i.val j.val ≤ g.val)
    (hhi : g.val < max i.val j.val) : g ∈ selected := by
  classical
  by_contra hg
  have hindex : componentIndex selected i = componentIndex selected j :=
    congrArg Fin.val hlabel
  let A : Finset (Fin 2024) :=
    (Finset.univ \ selected).filter (fun u => u.val < i.val)
  let B : Finset (Fin 2024) :=
    (Finset.univ \ selected).filter (fun u => u.val < j.val)
  by_cases hij : i.val ≤ j.val
  · have hij' : i.val < j.val := by
      by_contra h
      have heq : i.val = j.val := by omega
      rw [heq] at hlo hhi
      omega
    have hABsub : A ⊆ B := by
      intro u hu
      simp only [A, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and] at hu
      simp only [B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      exact ⟨hu.1, lt_of_lt_of_le hu.2 hij⟩
    have hAB : A ⊂ B := by
      apply (Finset.ssubset_iff_of_subset hABsub).2
      refine ⟨g, ?_, ?_⟩
      · simp only [B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and]
        refine ⟨hg, ?_⟩
        have hmax : max i.val j.val = j.val := max_eq_right hij
        omega
      · simp only [A, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and]
        intro hgi
        have hmin : min i.val j.val = i.val := min_eq_left hij
        omega
    have hcard := Finset.card_lt_card hAB
    exact (Nat.ne_of_lt hcard) hindex
  · have hji : j.val < i.val := lt_of_not_ge hij
    have hBAsub : B ⊆ A := by
      intro u hu
      simp only [B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and] at hu
      simp only [A, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      exact ⟨hu.1, lt_of_lt_of_le hu.2 hji.le⟩
    have hBA : B ⊂ A := by
      apply (Finset.ssubset_iff_of_subset hBAsub).2
      refine ⟨g, ?_, ?_⟩
      · simp only [A, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and]
        refine ⟨hg, ?_⟩
        have hmax : max i.val j.val = i.val := max_eq_left hji.le
        omega
      · simp only [B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and]
        intro hgj
        have hmin : min i.val j.val = j.val := min_eq_right hji.le
        omega
    have hcard := Finset.card_lt_card hBA
    exact (Nat.ne_of_gt hcard) hindex
private noncomputable def blackComponentLabel
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (_hvalid : IsValidConfiguration 2025 all_black partition)
    (H V : Finset (Fin 2024)) (p : ↥all_black) :
    Fin (2025 - H.card) × Fin (2025 - V.card) :=
  (componentLabel H p.1.2, componentLabel V p.1.1)

private lemma compatible_component_black_injective_of_crossing
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (H V : Finset (Fin 2024))
    (hcross : ∀ p q : ↥all_black,
      (∀ g : Fin 2024, min (py p.1) (py q.1) ≤ g.val →
        g.val < max (py p.1) (py q.1) → g ∈ H) →
      (∀ g : Fin 2024, min (px p.1) (px q.1) ≤ g.val →
        g.val < max (px p.1) (px q.1) → g ∈ V) → p = q) :
    Function.Injective (blackComponentLabel hvalid H V) := by
  intro p q hpq
  apply hcross p q
  · intro g hlo hhi
    apply selected_between_of_componentLabel_eq H p.1.2 q.1.2
    · exact congrArg Prod.fst hpq
    · exact hlo
    · exact hhi
  · intro g hlo hhi
    apply selected_between_of_componentLabel_eq V p.1.1 q.1.1
    · exact congrArg Prod.snd hpq
    · exact hlo
    · exact hhi

private lemma component_product_bound_of_injective
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (H V : Finset (Fin 2024))
    (hinj : Function.Injective (blackComponentLabel hvalid H V)) :
    2025 ≤ (2025 - H.card) * (2025 - V.card) := by
  have hcard := Fintype.card_le_of_injective (blackComponentLabel hvalid H V) hinj
  simpa [Fintype.card_prod, hvalid.1] using hcard



private lemma component_sum_lower_bound {a b : ℕ} (hblack : 2025 ≤ a * b) :
    90 ≤ a + b := by
  have hamgm : 4 * a * b ≤ (a + b) ^ 2 := four_mul_le_sq_add a b
  by_contra h
  have hsum : a + b ≤ 89 := by omega
  have hsquare : (a + b) ^ 2 ≤ 89 ^ 2 := Nat.pow_le_pow_left hsum 2
  nlinarith

private lemma compatible_card_upper_bound
    {H V : Finset (Fin 2024)}
    (hblack : 2025 ≤ (2025 - H.card) * (2025 - V.card)) :
    H.card + V.card ≤ 3960 := by
  have hH : H.card ≤ 2024 := by simpa using H.card_le_univ
  have hV : V.card ≤ 2024 := by simpa using V.card_le_univ
  have hsum := component_sum_lower_bound hblack
  omega

private lemma seam_tangent_arithmetic
    {pieces sh sv crossings Ah Av H V conflicts : ℕ}
    (hidentity : pieces + 2025 = 1 + sh + sv + crossings)
    (hhorizontal : 4048 ≤ sh + Ah) (hvertical : 4048 ≤ sv + Av)
    (hdelete : Ah ≤ H + conflicts) (hkeep : Av = V)
    (hinject : conflicts ≤ crossings) :
    6072 ≤ pieces + H + V := by
  omega

private lemma final_lower_bound_arithmetic
    {pieces h v : ℕ} (hlower : 6072 ≤ pieces + h + v)
    (hupper : h + v ≤ 3960) : 2112 ≤ pieces := by
  omega

private abbrev Gap := Fin 2024

private def gapLow (g : Gap) : Fin 2025 := ⟨g.val, by omega⟩
private def gapHigh (g : Gap) : Fin 2025 := ⟨g.val + 1, by omega⟩

private def lo (a b : Fin 2025) : Fin 2025 := min a b
private def hi (a b : Fin 2025) : Fin 2025 := max a b

private lemma gapLow_ne_gapHigh (g : Gap) : gapLow g ≠ gapHigh g := by
  intro h
  have hv := congrArg Fin.val h
  simp [gapLow, gapHigh] at hv

private lemma lo_lt_hi {a b : Fin 2025} (hne : a ≠ b) :
    (lo a b).val < (hi a b).val := by
  have hval : a.val ≠ b.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hab | hba
  · simpa [lo, hi, min_eq_left hab.le, max_eq_right hab.le]
  · simpa [lo, hi, min_eq_right hba.le, max_eq_left hba.le]

private lemma predicate_at_lo {f : Fin 2025 → Prop} {a b : Fin 2025}
    (ha : f a) (hb : f b) : f (lo a b) := by
  by_cases hab : a ≤ b
  · simpa [lo, min_eq_left hab] using ha
  · have hba : b ≤ a := le_of_not_ge hab
    simpa [lo, min_eq_right hba] using hb

private lemma predicate_at_hi {f : Fin 2025 → Prop} {a b : Fin 2025}
    (ha : f a) (hb : f b) : f (hi a b) := by
  by_cases hab : a ≤ b
  · simpa [hi, max_eq_right hab] using hb
  · have hba : b ≤ a := le_of_not_ge hab
    simpa [hi, max_eq_left hba] using ha

/-! ### Canonical owners and the black permutation -/

private abbrev TangentPiece (all_black : Finset (Point 2025))
    (partition : Finset (Matilda 2025 all_black)) :=
  {m // m ∈ partition} ⊕ {p // p ∈ all_black}

private noncomputable def tangentPieceOwner
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hcover : ∀ p : Point 2025, p ∉ all_black → ∃! m ∈ partition, m.mem p)
    (p : Point 2025) : TangentPiece all_black partition :=
  if hp : p ∈ all_black then Sum.inr ⟨p, hp⟩
  else Sum.inl ⟨Classical.choose (hcover p hp),
    (Classical.choose_spec (hcover p hp)).1.1⟩

private lemma tangentPieceOwner_of_black
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hcover : ∀ p : Point 2025, p ∉ all_black → ∃! m ∈ partition, m.mem p)
    (p : Point 2025) (hp : p ∈ all_black) :
    tangentPieceOwner hcover p = Sum.inr ⟨p, hp⟩ := by
  simp [tangentPieceOwner, hp]

private lemma tangentPieceOwner_ne_black_white
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hcover : ∀ p : Point 2025, p ∉ all_black → ∃! m ∈ partition, m.mem p)
    {p q : Point 2025} (hp : p ∈ all_black) (hq : q ∉ all_black) :
    tangentPieceOwner hcover p ≠ tangentPieceOwner hcover q := by
  rw [tangentPieceOwner_of_black hcover p hp]
  simp [tangentPieceOwner, hq]

private lemma tangentBlackColumn_bijective
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Function.Bijective (fun p : ↥all_black => p.1.1) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro p q hpq
    apply Subtype.ext
    exact hvalid.2.1 p.1 p.2 q.1 q.2 (congrArg Fin.val hpq)
  · simpa using hvalid.1

private lemma tangentBlackRow_bijective
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Function.Bijective (fun p : ↥all_black => p.1.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro p q hpq
    apply Subtype.ext
    exact hvalid.2.2.1 p.1 p.2 q.1 q.2 (congrArg Fin.val hpq)
  · simpa using hvalid.1

private noncomputable def tangentBlackColumnEquiv
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    ↥all_black ≃ Fin 2025 :=
  Equiv.ofBijective (fun p : ↥all_black => p.1.1)
    (tangentBlackColumn_bijective hvalid)

private noncomputable def tangentBlackRowEquiv
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    ↥all_black ≃ Fin 2025 :=
  Equiv.ofBijective (fun p : ↥all_black => p.1.2)
    (tangentBlackRow_bijective hvalid)

private noncomputable def tangentBlackPermutation
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Equiv.Perm (Fin 2025) :=
  (tangentBlackColumnEquiv hvalid).symm.trans (tangentBlackRowEquiv hvalid)

private lemma tangentBlackPermutation_point
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (x : Fin 2025) :
    (x, tangentBlackPermutation hvalid x) ∈ all_black := by
  have hp := ((tangentBlackColumnEquiv hvalid).symm x).2
  convert hp using 1
  apply Prod.ext
  · exact ((tangentBlackColumnEquiv hvalid).apply_symm_apply x).symm
  · rfl

private lemma tangentBlackPermutation_symm_point
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (y : Fin 2025) :
    ((tangentBlackPermutation hvalid).symm y, y) ∈ all_black := by
  simpa using tangentBlackPermutation_point hvalid
    ((tangentBlackPermutation hvalid).symm y)

private lemma tangent_not_black_same_column
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    {p q : Point 2025} (hp : p ∈ all_black) (hx : px p = px q) (hne : p ≠ q) :
    q ∉ all_black := by
  intro hq
  apply hne
  exact hvalid.2.1 p hp q hq hx

private lemma tangent_not_black_same_row
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    {p q : Point 2025} (hp : p ∈ all_black) (hy : py p = py q) (hne : p ≠ q) :
    q ∉ all_black := by
  intro hq
  apply hne
  exact hvalid.2.2.1 p hp q hq hy

/-! ### Horizontal and vertical unit seams -/

private noncomputable def horizontalSeam
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (g : Gap) (x : Fin 2025) : Prop :=
  tangentPieceOwner hvalid.2.2.2 (x, gapLow g) ≠
    tangentPieceOwner hvalid.2.2.2 (x, gapHigh g)

private noncomputable def verticalSeam
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (g : Gap) (y : Fin 2025) : Prop :=
  tangentPieceOwner hvalid.2.2.2 (gapLow g, y) ≠
    tangentPieceOwner hvalid.2.2.2 (gapHigh g, y)

private lemma horizontalSeam_at_low_row_black
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) :
    horizontalSeam hvalid g ((tangentBlackPermutation hvalid).symm (gapLow g)) := by
  let x := (tangentBlackPermutation hvalid).symm (gapLow g)
  let p : Point 2025 := (x, gapLow g)
  let q : Point 2025 := (x, gapHigh g)
  have hp : p ∈ all_black := by
    simpa [p, x] using tangentBlackPermutation_symm_point hvalid (gapLow g)
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg (fun z : Point 2025 => z.2.val) h
    simp [p, q, gapLow, gapHigh] at hv
  have hq : q ∉ all_black :=
    tangent_not_black_same_column hvalid hp (by rfl) hpq
  exact tangentPieceOwner_ne_black_white hvalid.2.2.2 hp hq

private lemma horizontalSeam_at_high_row_black
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) :
    horizontalSeam hvalid g ((tangentBlackPermutation hvalid).symm (gapHigh g)) := by
  let x := (tangentBlackPermutation hvalid).symm (gapHigh g)
  let p : Point 2025 := (x, gapHigh g)
  let q : Point 2025 := (x, gapLow g)
  have hp : p ∈ all_black := by
    simpa [p, x] using tangentBlackPermutation_symm_point hvalid (gapHigh g)
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg (fun z : Point 2025 => z.2.val) h
    simp [p, q, gapLow, gapHigh] at hv
  have hq : q ∉ all_black :=
    tangent_not_black_same_column hvalid hp (by rfl) hpq
  exact (tangentPieceOwner_ne_black_white hvalid.2.2.2 hp hq).symm

private lemma verticalSeam_at_low_column_black
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) :
    verticalSeam hvalid g (tangentBlackPermutation hvalid (gapLow g)) := by
  let y := tangentBlackPermutation hvalid (gapLow g)
  let p : Point 2025 := (gapLow g, y)
  let q : Point 2025 := (gapHigh g, y)
  have hp : p ∈ all_black := by
    simpa [p, y] using tangentBlackPermutation_point hvalid (gapLow g)
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg (fun z : Point 2025 => z.1.val) h
    simp [p, q, gapLow, gapHigh] at hv
  have hq : q ∉ all_black :=
    tangent_not_black_same_row hvalid hp (by rfl) hpq
  exact tangentPieceOwner_ne_black_white hvalid.2.2.2 hp hq

private lemma verticalSeam_at_high_column_black
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) :
    verticalSeam hvalid g (tangentBlackPermutation hvalid (gapHigh g)) := by
  let y := tangentBlackPermutation hvalid (gapHigh g)
  let p : Point 2025 := (gapHigh g, y)
  let q : Point 2025 := (gapLow g, y)
  have hp : p ∈ all_black := by
    simpa [p, y] using tangentBlackPermutation_point hvalid (gapHigh g)
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg (fun z : Point 2025 => z.1.val) h
    simp [p, q, gapLow, gapHigh] at hv
  have hq : q ∉ all_black :=
    tangent_not_black_same_row hvalid hp (by rfl) hpq
  exact (tangentPieceOwner_ne_black_white hvalid.2.2.2 hp hq).symm

private lemma horizontalEndpoint_ne
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) :
    (tangentBlackPermutation hvalid).symm (gapLow g) ≠
      (tangentBlackPermutation hvalid).symm (gapHigh g) :=
  (tangentBlackPermutation hvalid).symm.injective.ne (gapLow_ne_gapHigh g)

private lemma verticalEndpoint_ne
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) :
    tangentBlackPermutation hvalid (gapLow g) ≠
      tangentBlackPermutation hvalid (gapHigh g) :=
  (tangentBlackPermutation hvalid).injective.ne (gapLow_ne_gapHigh g)

/-! ### Supported adjacent-row and adjacent-column tangents -/

private def IsSupportedBetween (seam : Fin 2025 → Prop) (a b : Fin 2025) : Prop :=
  ∀ x : Fin 2025, (lo a b).val < x.val → x.val < (hi a b).val → seam x

private lemma supportedBetween_of_adjacent {seam : Fin 2025 → Prop} {a b : Fin 2025}
    (hadj : (hi a b).val = (lo a b).val + 1) : IsSupportedBetween seam a b := by
  intro x hxlo hxhi
  omega

private noncomputable def IsHorizontalTangentSupported
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) : Prop :=
  IsSupportedBetween (horizontalSeam hvalid g)
    ((tangentBlackPermutation hvalid).symm (gapLow g))
    ((tangentBlackPermutation hvalid).symm (gapHigh g))

private noncomputable def IsVerticalTangentSupported
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) : Prop :=
  IsSupportedBetween (verticalSeam hvalid g)
    (tangentBlackPermutation hvalid (gapLow g))
    (tangentBlackPermutation hvalid (gapHigh g))

private lemma horizontal_diagonal_tangent_supported
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap)
    (hdiag : (hi ((tangentBlackPermutation hvalid).symm (gapLow g))
      ((tangentBlackPermutation hvalid).symm (gapHigh g))).val =
      (lo ((tangentBlackPermutation hvalid).symm (gapLow g))
        ((tangentBlackPermutation hvalid).symm (gapHigh g))).val + 1) :
    IsHorizontalTangentSupported hvalid g :=
  supportedBetween_of_adjacent hdiag

private lemma vertical_diagonal_tangent_supported
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap)
    (hdiag : (hi (tangentBlackPermutation hvalid (gapLow g))
      (tangentBlackPermutation hvalid (gapHigh g))).val =
      (lo (tangentBlackPermutation hvalid (gapLow g))
        (tangentBlackPermutation hvalid (gapHigh g))).val + 1) :
    IsVerticalTangentSupported hvalid g :=
  supportedBetween_of_adjacent hdiag

private noncomputable def Ah
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) : Finset Gap := by
  classical
  exact Finset.univ.filter (IsHorizontalTangentSupported hvalid)

private noncomputable def Av
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) : Finset Gap := by
  classical
  exact Finset.univ.filter (IsVerticalTangentSupported hvalid)

/-! ### Finite seam runs and explicit Sigma aggregation -/

private def tangentNatRunStarts (n : ℕ) (f : ℕ → Prop) [DecidablePred f] : Finset ℕ :=
  (Finset.range n).filter fun j => f j ∧ (j = 0 ∨ ¬ f (j - 1))

private lemma mem_tangentNatRunStarts {n : ℕ} (f : ℕ → Prop) [DecidablePred f]
    {j : ℕ} :
    j ∈ tangentNatRunStarts n f ↔
      j < n ∧ f j ∧ (j = 0 ∨ ¬ f (j - 1)) := by
  simp [tangentNatRunStarts]

private lemma tangentNatRunStarts_card_pos {n : ℕ} (f : ℕ → Prop)
    [DecidablePred f] {a : ℕ} (ha : a < n) (hfa : f a) :
    1 ≤ (tangentNatRunStarts n f).card := by
  let P : ℕ → Prop := fun j => j < n ∧ f j
  have hex : ∃ j, P j := ⟨a, ha, hfa⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have hjstart : j = 0 ∨ ¬ f (j - 1) := by
    by_cases hz : j = 0
    · exact Or.inl hz
    · right
      intro hf
      have hP : P (j - 1) := ⟨by omega, hf⟩
      exact (Nat.find_min hex (by omega)) hP
  apply Finset.one_le_card.mpr
  exact ⟨j, (mem_tangentNatRunStarts f).2 ⟨hj.1, hj.2, hjstart⟩⟩

private lemma tangentNatRunStarts_card_two_of_gap {n : ℕ} (f : ℕ → Prop)
    [DecidablePred f] {a b c : ℕ}
    (ha : a < n) (hb : b < n) (hac : a ≤ c) (hcb : c < b)
    (hfa : f a) (hfb : f b) (hfc : ¬ f c) :
    2 ≤ (tangentNatRunStarts n f).card := by
  let P : ℕ → Prop := fun j => j < n ∧ f j
  have hex₁ : ∃ j, P j := ⟨a, ha, hfa⟩
  let j₁ := Nat.find hex₁
  have hj₁ : P j₁ := Nat.find_spec hex₁
  have hj₁le : j₁ ≤ a := Nat.find_min' hex₁ ⟨ha, hfa⟩
  have hj₁start : j₁ = 0 ∨ ¬ f (j₁ - 1) := by
    by_cases hz : j₁ = 0
    · exact Or.inl hz
    · right
      intro hf
      have hP : P (j₁ - 1) := ⟨by omega, hf⟩
      exact (Nat.find_min hex₁ (by omega)) hP
  let Q : ℕ → Prop := fun j => c < j ∧ j < n ∧ f j
  have hex₂ : ∃ j, Q j := ⟨b, hcb, hb, hfb⟩
  let j₂ := Nat.find hex₂
  have hj₂ : Q j₂ := Nat.find_spec hex₂
  have hj₂start : j₂ = 0 ∨ ¬ f (j₂ - 1) := by
    right
    intro hf
    by_cases heq : j₂ - 1 = c
    · exact hfc (heq ▸ hf)
    · have hQ : Q (j₂ - 1) := ⟨by omega, by omega, hf⟩
      exact (Nat.find_min hex₂ (by omega)) hQ
  have hne : j₁ ≠ j₂ := by omega
  have hsub : {j₁, j₂} ⊆ tangentNatRunStarts n f := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact (mem_tangentNatRunStarts f).2 ⟨hj₁.1, hj₁.2, hj₁start⟩
    · exact (mem_tangentNatRunStarts f).2 ⟨hj₂.2.1, hj₂.2.2, hj₂start⟩
  rw [← Finset.card_pair hne]
  exact Finset.card_le_card hsub

private def finiteSeamSequence (seam : Fin 2025 → Prop) (j : ℕ) : Prop :=
  ∃ hj : j < 2025, seam ⟨j, hj⟩

private noncomputable def seamRunStarts (seam : Fin 2025 → Prop) : Finset ℕ := by
  classical
  exact tangentNatRunStarts 2025 (finiteSeamSequence seam)

private lemma seamRunStarts_card_pos (seam : Fin 2025 → Prop) (a : Fin 2025)
    (ha : seam a) : 1 ≤ (seamRunStarts seam).card := by
  classical
  have hseq : finiteSeamSequence seam a.val := ⟨a.isLt, by simpa using ha⟩
  simpa [seamRunStarts] using
    (tangentNatRunStarts_card_pos (finiteSeamSequence seam) a.isLt hseq)

private lemma seamRunStarts_card_two_of_not_supported
    (seam : Fin 2025 → Prop) (a b : Fin 2025) (hne : a ≠ b)
    (ha : seam a) (hb : seam b) (hunsupported : ¬ IsSupportedBetween seam a b) :
    2 ≤ (seamRunStarts seam).card := by
  classical
  have hlohi : (lo a b).val < (hi a b).val := lo_lt_hi hne
  have hlo : seam (lo a b) := predicate_at_lo ha hb
  have hhi : seam (hi a b) := predicate_at_hi ha hb
  have hmissing : ∃ x : Fin 2025,
      (lo a b).val < x.val ∧ x.val < (hi a b).val ∧ ¬ seam x := by
    simp only [IsSupportedBetween] at hunsupported
    push Not at hunsupported
    exact hunsupported
  obtain ⟨x, hxlo, hxhi, hxseam⟩ := hmissing
  have hseqlo : finiteSeamSequence seam (lo a b).val :=
    ⟨(lo a b).isLt, by simpa using hlo⟩
  have hseqhi : finiteSeamSequence seam (hi a b).val :=
    ⟨(hi a b).isLt, by simpa using hhi⟩
  have hxseq : ¬ finiteSeamSequence seam x.val := by
    rintro ⟨_, hxs⟩
    exact hxseam (by simpa using hxs)
  simpa [seamRunStarts] using
    (tangentNatRunStarts_card_two_of_gap (finiteSeamSequence seam)
      (ha := (lo a b).isLt) (hb := (hi a b).isLt)
      (hac := Nat.le_of_lt hxlo) (hcb := hxhi)
      hseqlo hseqhi hxseq)

private noncomputable def horizontalGapRunStarts
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) : Finset ℕ :=
  seamRunStarts (horizontalSeam hvalid g)

private noncomputable def verticalGapRunStarts
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) : Finset ℕ :=
  seamRunStarts (verticalSeam hvalid g)

private noncomputable def horizontalRuns
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Finset (Σ _ : Gap, ℕ) := by
  classical
  exact Finset.univ.sigma (horizontalGapRunStarts hvalid)

private noncomputable def verticalRuns
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Finset (Σ _ : Gap, ℕ) := by
  classical
  exact Finset.univ.sigma (verticalGapRunStarts hvalid)

private def sigmaRunMembershipEquiv (runs : Gap → Finset ℕ) :
    (Σ g : Gap, {j : ℕ // j ∈ runs g}) ≃
      {z : Σ _ : Gap, ℕ // z ∈ Finset.univ.sigma runs} where
  toFun z := ⟨⟨z.1, z.2.1⟩,
    Finset.mem_sigma.mpr ⟨Finset.mem_univ _, z.2.2⟩⟩
  invFun z := ⟨z.1.1, ⟨z.1.2, (Finset.mem_sigma.mp z.2).2⟩⟩
  left_inv := by
    rintro ⟨g, ⟨j, hj⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨g, j⟩, hj⟩
    rfl

private lemma sigmaRuns_card (runs : Gap → Finset ℕ) :
    (Finset.univ.sigma runs).card = ∑ g : Gap, (runs g).card := by
  classical
  have hcard := Fintype.card_congr (sigmaRunMembershipEquiv runs)
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_coe] at hcard
  exact hcard.symm

private lemma horizontalGap_run_supported_bound
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) :
    2 ≤ (horizontalGapRunStarts hvalid g).card +
      if g ∈ Ah hvalid then 1 else 0 := by
  classical
  by_cases hg : g ∈ Ah hvalid
  · have hr := seamRunStarts_card_pos (horizontalSeam hvalid g)
      ((tangentBlackPermutation hvalid).symm (gapLow g))
      (horizontalSeam_at_low_row_black hvalid g)
    rw [if_pos hg]
    simpa [horizontalGapRunStarts] using Nat.add_le_add_right hr 1
  · have hunsupported : ¬ IsHorizontalTangentSupported hvalid g := by
      intro hs
      apply hg
      simp only [Ah, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hs
    have hr := seamRunStarts_card_two_of_not_supported
      (horizontalSeam hvalid g)
      ((tangentBlackPermutation hvalid).symm (gapLow g))
      ((tangentBlackPermutation hvalid).symm (gapHigh g))
      (horizontalEndpoint_ne hvalid g)
      (horizontalSeam_at_low_row_black hvalid g)
      (horizontalSeam_at_high_row_black hvalid g)
      hunsupported
    rw [if_neg hg, Nat.add_zero]
    simpa [horizontalGapRunStarts] using hr

private lemma verticalGap_run_supported_bound
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) :
    2 ≤ (verticalGapRunStarts hvalid g).card +
      if g ∈ Av hvalid then 1 else 0 := by
  classical
  by_cases hg : g ∈ Av hvalid
  · have hr := seamRunStarts_card_pos (verticalSeam hvalid g)
      (tangentBlackPermutation hvalid (gapLow g))
      (verticalSeam_at_low_column_black hvalid g)
    rw [if_pos hg]
    simpa [verticalGapRunStarts] using Nat.add_le_add_right hr 1
  · have hunsupported : ¬ IsVerticalTangentSupported hvalid g := by
      intro hs
      apply hg
      simp only [Av, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hs
    have hr := seamRunStarts_card_two_of_not_supported
      (verticalSeam hvalid g)
      (tangentBlackPermutation hvalid (gapLow g))
      (tangentBlackPermutation hvalid (gapHigh g))
      (verticalEndpoint_ne hvalid g)
      (verticalSeam_at_low_column_black hvalid g)
      (verticalSeam_at_high_column_black hvalid g)
      hunsupported
    rw [if_neg hg, Nat.add_zero]
    simpa [verticalGapRunStarts] using hr

private lemma sum_gap_run_supported_bound
    (runs : Gap → Finset ℕ) (supported : Finset Gap)
    (hgap : ∀ g : Gap,
      2 ≤ (runs g).card + if g ∈ supported then 1 else 0) :
    4048 ≤ (Finset.univ.sigma runs).card + supported.card := by
  classical
  have hindicator : (∑ g : Gap, if g ∈ supported then 1 else 0) = supported.card := by
    rw [← Finset.sum_filter]
    simp
  calc
    4048 = ∑ _g : Gap, 2 := by norm_num
    _ ≤ ∑ g : Gap, ((runs g).card + if g ∈ supported then 1 else 0) := by
      exact Finset.sum_le_sum fun g _ => hgap g
    _ = (Finset.univ.sigma runs).card + supported.card := by
      rw [Finset.sum_add_distrib, ← sigmaRuns_card, hindicator]

private lemma horizontal_supported_run_count
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    4048 ≤ (horizontalRuns hvalid).card + (Ah hvalid).card := by
  simpa [horizontalRuns] using
    sum_gap_run_supported_bound (horizontalGapRunStarts hvalid) (Ah hvalid)
      (horizontalGap_run_supported_bound hvalid)

private lemma vertical_supported_run_count
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    4048 ≤ (verticalRuns hvalid).card + (Av hvalid).card := by
  simpa [verticalRuns] using
    sum_gap_run_supported_bound (verticalGapRunStarts hvalid) (Av hvalid)
      (verticalGap_run_supported_bound hvalid)

private lemma configuration_intermediate_bound
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (hhorizontal : 4048 ≤
      (horizontalRunStarts
        (configurationOwner all_black partition hvalid)).card +
      (supportedRowTangents
        (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid)).card)
    (hvertical : 4048 ≤
      (verticalRunStarts
        (configurationOwner all_black partition hvalid)).card +
      (supportedColumnTangents
        (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid)).card) :
    6072 ≤ partition.card +
      (compatibleRowTangents
        (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid)).card +
      (compatibleColumnTangents
        (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid)).card := by
  let owner := configurationOwner all_black partition hvalid
  let σ := blackPermutationEquiv hvalid
  apply seam_tangent_arithmetic (configuration_seam_identity hvalid)
    hhorizontal hvertical
  · exact supportedRowTangents_card_le_compatible_add_conflicts owner σ
  · rfl
  · exact tangentConflicts_card_le_crossings owner σ

/-- The geometric part of the compatible-tangent argument only has to provide
the product bound in this statement; all remaining numerical work is proved
above. -/
private lemma lower_bound_from_three_finite_lemmas
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (hhorizontal : 4048 ≤
      (horizontalRunStarts
        (configurationOwner all_black partition hvalid)).card +
      (supportedRowTangents
        (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid)).card)
    (hvertical : 4048 ≤
      (verticalRunStarts
        (configurationOwner all_black partition hvalid)).card +
      (supportedColumnTangents
        (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid)).card)
    (hcomponents : Function.Injective
      (blackComponentLabel hvalid
        (compatibleRowTangents
          (configurationOwner all_black partition hvalid)
          (blackPermutationEquiv hvalid))
        (compatibleColumnTangents
          (configurationOwner all_black partition hvalid)
          (blackPermutationEquiv hvalid)))) :
    2112 ≤ partition.card := by
  have hintermediate := configuration_intermediate_bound hvalid hhorizontal hvertical
  have hproduct := component_product_bound_of_injective hvalid _ _ hcomponents
  apply final_lower_bound_arithmetic hintermediate
  exact compatible_card_upper_bound hproduct


private abbrev LowerGap := Fin 2024

private def lowerGapLo (g : LowerGap) : Fin 2025 := g.castSucc
private def lowerGapHi (g : LowerGap) : Fin 2025 := g.succ
/-! ## Compatible tangents and interval blocks -/

/-- The cut after `g` is crossed exactly when the endpoints lie on opposite
sides of that cut.  The upper side is half-open, which makes this definition
work uniformly at an endpoint. -/
private def CrossesCut (a b : Fin 2025) (g : LowerGap) : Prop :=
  min a.val b.val ≤ g.val ∧ g.val < max a.val b.val

private def intervalBlockStarts (selected : Finset LowerGap) : Finset (Fin 2025) :=
  insert 0 ((Finset.univ \ selected).image lowerGapHi)

private def intervalBlockIndex (selected : Finset LowerGap) (i : Fin 2025) : ℕ :=
  ((Finset.univ \ selected).filter (fun g => g.val < i.val)).card

private lemma intervalBlockIndex_le (selected : Finset LowerGap) (i : Fin 2025) :
    intervalBlockIndex selected i ≤ 2024 - selected.card := by
  classical
  calc
    intervalBlockIndex selected i ≤ (Finset.univ \ selected).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2024 - selected.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ selected)]
      simp

private lemma intervalBlockIndex_lt (selected : Finset LowerGap) (i : Fin 2025) :
    intervalBlockIndex selected i < 2025 - selected.card := by
  have hcard : selected.card ≤ 2024 := by simpa using selected.card_le_univ
  have hle := intervalBlockIndex_le selected i
  omega

private def blockOf (selected : Finset LowerGap) (i : Fin 2025) :
    Fin (2025 - selected.card) :=
  ⟨intervalBlockIndex selected i, intervalBlockIndex_lt selected i⟩

private lemma lowerGapHi_injective : Function.Injective lowerGapHi := by
  intro g h heq
  apply Fin.ext
  have := congrArg Fin.val heq
  simpa [lowerGapHi] using this

private lemma intervalBlockStarts_card (selected : Finset LowerGap) :
    (intervalBlockStarts selected).card = 2025 - selected.card := by
  classical
  have hzero : (0 : Fin 2025) ∉ (Finset.univ \ selected).image lowerGapHi := by
    intro h
    obtain ⟨g, hg, heq⟩ := Finset.mem_image.1 h
    have := congrArg Fin.val heq
    simp [lowerGapHi] at this
  rw [intervalBlockStarts, Finset.card_insert_of_notMem hzero,
    Finset.card_image_of_injective _ lowerGapHi_injective,
    Finset.card_sdiff_of_subset (Finset.subset_univ selected)]
  have hcard : selected.card ≤ 2024 := by simpa using selected.card_le_univ
  simp
  omega

private lemma blockOf_eq_iff (selected : Finset LowerGap) (i j : Fin 2025) :
    blockOf selected i = blockOf selected j ↔
      ∀ g : LowerGap, min i.val j.val ≤ g.val →
        g.val < max i.val j.val → g ∈ selected := by
  classical
  constructor
  · intro heq g hlo hhi
    have hindex : intervalBlockIndex selected i = intervalBlockIndex selected j :=
      congrArg Fin.val heq
    by_cases hij : i.val ≤ j.val
    · have hgi : i.val ≤ g.val := by simpa [min_eq_left hij] using hlo
      have hgj : g.val < j.val := by simpa [max_eq_right hij] using hhi
      by_contra hgsel
      let A := (Finset.univ \ selected).filter (fun x => x.val < i.val)
      let B := (Finset.univ \ selected).filter (fun x => x.val < j.val)
      have hgB : g ∈ B := by simp [B, hgsel, hgj]
      have hsub : A ⊆ B.erase g := by
        intro x hx
        have hxparts := Finset.mem_filter.1 hx
        apply Finset.mem_erase.2
        refine ⟨?_, Finset.mem_filter.2 ⟨hxparts.1, ?_⟩⟩
        · intro hxg
          subst x
          omega
        · omega
      have hcardle := Finset.card_le_card hsub
      have herase := Finset.card_erase_add_one hgB
      change A.card = B.card at hindex
      omega
    · have hji : j.val ≤ i.val := by omega
      have hgj : j.val ≤ g.val := by simpa [min_eq_right hji] using hlo
      have hgi : g.val < i.val := by simpa [max_eq_left hji] using hhi
      by_contra hgsel
      let A := (Finset.univ \ selected).filter (fun x => x.val < j.val)
      let B := (Finset.univ \ selected).filter (fun x => x.val < i.val)
      have hgB : g ∈ B := by simp [B, hgsel, hgi]
      have hsub : A ⊆ B.erase g := by
        intro x hx
        have hxparts := Finset.mem_filter.1 hx
        apply Finset.mem_erase.2
        refine ⟨?_, Finset.mem_filter.2 ⟨hxparts.1, ?_⟩⟩
        · intro hxg
          subst x
          omega
        · omega
      have hcardle := Finset.card_le_card hsub
      have herase := Finset.card_erase_add_one hgB
      change B.card = A.card at hindex
      omega
  · intro hselected
    apply Fin.ext
    change intervalBlockIndex selected i = intervalBlockIndex selected j
    unfold intervalBlockIndex
    apply congrArg Finset.card
    ext g
    simp only [Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hnot, hgi⟩
      refine ⟨hnot, ?_⟩
      by_contra hgj
      have hjg : j.val ≤ g.val := by omega
      have hij : j.val < i.val := by omega
      have hlo : min i.val j.val ≤ g.val := by
        rw [min_eq_right hij.le]
        exact hjg
      have hhi : g.val < max i.val j.val := by
        rw [max_eq_left hij.le]
        exact hgi
      exact hnot (hselected g hlo hhi)
    · rintro ⟨hnot, hgj⟩
      refine ⟨hnot, ?_⟩
      by_contra hgi
      have hig : i.val ≤ g.val := by omega
      have hij : i.val < j.val := by omega
      have hlo : min i.val j.val ≤ g.val := by
        rw [min_eq_left hij.le]
        exact hig
      have hhi : g.val < max i.val j.val := by
        rw [max_eq_right hij.le]
        exact hgj
      exact hnot (hselected g hlo hhi)

private def natToFin2025 (x : ℕ) : Fin 2025 :=
  ⟨x % 2025, Nat.mod_lt _ (by omega)⟩

private lemma natToFin2025_val {x : ℕ} (hx : x < 2025) :
    (natToFin2025 x).val = x := by
  exact Nat.mod_eq_of_lt hx

private lemma adjacent_low_high {f : ℕ → ℕ} {i j a b : ℕ}
    (hij : i < j) (hleft : f i ≤ a) (hright : b ≤ f j)
    (houtside : ∀ k, i < k → k < j → f k ≤ a ∨ b ≤ f k) :
    ∃ g, i ≤ g ∧ g < j ∧ f g ≤ a ∧ b ≤ f (g + 1) := by
  classical
  let P : ℕ → Prop := fun t => i < t ∧ t ≤ j ∧ b ≤ f t
  have hex : ∃ t, P t := ⟨j, hij, le_rfl, hright⟩
  let t := Nat.find hex
  have ht : P t := Nat.find_spec hex
  let g := t - 1
  have hgt : g + 1 = t := by dsimp [g]; omega
  have hgi : i ≤ g := by dsimp [g]; omega
  have hgj : g < j := by dsimp [g]; omega
  have hlow : f g ≤ a := by
    by_cases hgeq : g = i
    · simpa [hgeq] using hleft
    · have hgint : i < g ∧ g < j := ⟨by omega, hgj⟩
      rcases houtside g hgint.1 hgint.2 with hlow | hhigh
      · exact hlow
      · exfalso
        have hPg : P g := ⟨hgint.1, hgj.le, hhigh⟩
        exact (Nat.find_min hex (by omega)) hPg
  exact ⟨g, hgi, hgj, hlow, by simpa [hgt] using ht.2.2⟩

private lemma adjacent_high_low {f : ℕ → ℕ} {i j a b : ℕ}
    (hij : i < j) (hleft : b ≤ f i) (hright : f j ≤ a)
    (houtside : ∀ k, i < k → k < j → f k ≤ a ∨ b ≤ f k) :
    ∃ g, i ≤ g ∧ g < j ∧ b ≤ f g ∧ f (g + 1) ≤ a := by
  classical
  let P : ℕ → Prop := fun t => i < t ∧ t ≤ j ∧ f t ≤ a
  have hex : ∃ t, P t := ⟨j, hij, le_rfl, hright⟩
  let t := Nat.find hex
  have ht : P t := Nat.find_spec hex
  let g := t - 1
  have hgt : g + 1 = t := by dsimp [g]; omega
  have hgi : i ≤ g := by dsimp [g]; omega
  have hgj : g < j := by dsimp [g]; omega
  have hhigh : b ≤ f g := by
    by_cases hgeq : g = i
    · simpa [hgeq] using hleft
    · have hgint : i < g ∧ g < j := ⟨by omega, hgj⟩
      rcases houtside g hgint.1 hgint.2 with hlow | hhigh
      · exfalso
        have hPg : P g := ⟨hgint.1, hgj.le, hlow⟩
        exact (Nat.find_min hex (by omega)) hPg
      · exact hhigh
  exact ⟨g, hgi, hgj, hhigh, by simpa [hgt] using ht.2.2⟩

/-- Two permutation points at opposite corners of a row/column interval force
an internal row edge and an internal column edge to cross the same unit cell. -/
private lemma permutation_discrete_crossing (σ : Equiv.Perm (Fin 2025))
    (i j : Fin 2025) (hij : i.val < j.val) :
    ∃ h v : LowerGap,
      i.val ≤ h.val ∧ h.val < j.val ∧
      min (σ i).val (σ j).val ≤ v.val ∧
      v.val < max (σ i).val (σ j).val ∧
      CrossesCut (σ (lowerGapLo h)) (σ (lowerGapHi h)) v ∧
      CrossesCut (σ.symm (lowerGapLo v)) (σ.symm (lowerGapHi v)) h := by
  classical
  by_cases hinter : ∃ k : Fin 2025,
      i.val < k.val ∧ k.val < j.val ∧
      min (σ i).val (σ j).val < (σ k).val ∧
      (σ k).val < max (σ i).val (σ j).val
  · obtain ⟨k, hik, hkj, hklo, hkhi⟩ := hinter
    obtain ⟨h, v, hih, hhk, hvlo, hvhi, hrow, hcol⟩ :=
      permutation_discrete_crossing σ i k hik
    refine ⟨h, v, hih, hhk.trans hkj, ?_, ?_, hrow, hcol⟩
    · have hmin : min (σ i).val (σ j).val ≤ min (σ i).val (σ k).val := by
        exact le_min (min_le_left _ _) hklo.le
      exact hmin.trans hvlo
    · have hmax : max (σ i).val (σ k).val ≤ max (σ i).val (σ j).val := by
        exact max_le (le_max_left _ _) hkhi.le
      exact hvhi.trans_le hmax
  · let a := min (σ i).val (σ j).val
    let b := max (σ i).val (σ j).val
    have hne : (σ i).val ≠ (σ j).val := by
      intro h
      have hs : σ i = σ j := Fin.ext h
      exact (Fin.ne_of_lt hij) (σ.injective hs)
    have hab : a < b := by dsimp [a, b]; omega
    let row : ℕ → ℕ := fun x => (σ (natToFin2025 x)).val
    let col : ℕ → ℕ := fun x => (σ.symm (natToFin2025 x)).val
    have hrowi : row i.val = (σ i).val := by
      apply congrArg (fun z : Fin 2025 => (σ z).val)
      apply Fin.ext
      exact natToFin2025_val i.isLt
    have hrowj : row j.val = (σ j).val := by
      apply congrArg (fun z : Fin 2025 => (σ z).val)
      apply Fin.ext
      exact natToFin2025_val j.isLt
    have hrowOutside : ∀ k, i.val < k → k < j.val → row k ≤ a ∨ b ≤ row k := by
      intro k hik hkj
      have hklt : k < 2025 := hkj.trans j.isLt
      have hkval : (natToFin2025 k).val = k := natToFin2025_val hklt
      by_contra hout
      push Not at hout
      apply hinter
      refine ⟨natToFin2025 k, ?_, ?_, ?_, ?_⟩
      · simpa [hkval] using hik
      · simpa [hkval] using hkj
      · simpa [a, row] using hout.1
      · simpa [b, row] using hout.2
    have hmina : a = (σ i).val ∨ a = (σ j).val := by
      dsimp [a]
      exact min_choice _ _
    have hmaxb : b = (σ i).val ∨ b = (σ j).val := by
      dsimp [b]
      exact max_choice _ _
    have hcoli : col a = i.val ∨ col a = j.val := by
      rcases hmina with ha | ha
      · left
        have halt : a < 2025 := by rw [ha]; exact (σ i).isLt
        have hafin : natToFin2025 a = σ i := by
          apply Fin.ext
          rw [natToFin2025_val halt, ha]
        simp [col, hafin]
      · right
        have halt : a < 2025 := by rw [ha]; exact (σ j).isLt
        have hafin : natToFin2025 a = σ j := by
          apply Fin.ext
          rw [natToFin2025_val halt, ha]
        simp [col, hafin]
    have hcolb : col b = i.val ∨ col b = j.val := by
      rcases hmaxb with hb | hb
      · left
        have hblt : b < 2025 := by rw [hb]; exact (σ i).isLt
        have hbfin : natToFin2025 b = σ i := by
          apply Fin.ext
          rw [natToFin2025_val hblt, hb]
        simp [col, hbfin]
      · right
        have hblt : b < 2025 := by rw [hb]; exact (σ j).isLt
        have hbfin : natToFin2025 b = σ j := by
          apply Fin.ext
          rw [natToFin2025_val hblt, hb]
        simp [col, hbfin]
    have hcolOutside : ∀ k, a < k → k < b → col k ≤ i.val ∨ j.val ≤ col k := by
      intro k hak hkb
      have hklt : k < 2025 := hkb.trans (by
        dsimp [b]
        exact max_lt (σ i).isLt (σ j).isLt)
      have hkval : (natToFin2025 k).val = k := natToFin2025_val hklt
      by_contra hout
      push Not at hout
      have hpoint := σ.apply_symm_apply (natToFin2025 k)
      apply hinter
      refine ⟨σ.symm (natToFin2025 k), ?_, ?_, ?_, ?_⟩
      · simpa [col] using hout.1
      · simpa [col] using hout.2
      · simpa [a, hkval, hpoint] using hak
      · simpa [b, hkval, hpoint] using hkb
    by_cases horder : (σ i).val < (σ j).val
    · have hrowEnds : row i.val ≤ a ∧ b ≤ row j.val := by
        rw [hrowi, hrowj]
        dsimp [a, b]
        omega
      obtain ⟨hg, hig, hgj, hglow, hghigh⟩ :=
        adjacent_low_high hij hrowEnds.1 hrowEnds.2 hrowOutside
      have hcolEnds : col a ≤ i.val ∧ j.val ≤ col b := by
        constructor
        · rcases hcoli with hai | haj
          · omega
          · exfalso
            have haeq : a = (σ i).val := by dsimp [a]; omega
            have hcolai : col a = i.val := by
              have halt : a < 2025 := by rw [haeq]; exact (σ i).isLt
              have hafin : natToFin2025 a = σ i := by
                apply Fin.ext
                rw [natToFin2025_val halt, haeq]
              simp [col, hafin]
            omega
        · rcases hcolb with hbi | hbj
          · exfalso
            have hbeq : b = (σ j).val := by dsimp [b]; omega
            have hcolbj : col b = j.val := by
              have hblt : b < 2025 := by rw [hbeq]; exact (σ j).isLt
              have hbfin : natToFin2025 b = σ j := by
                apply Fin.ext
                rw [natToFin2025_val hblt, hbeq]
              simp [col, hbfin]
            omega
          · omega
      obtain ⟨vg, hav, hvb, hvlow, hvhigh⟩ :=
        adjacent_low_high hab hcolEnds.1 hcolEnds.2 hcolOutside
      let h : LowerGap := ⟨hg, by omega⟩
      let v : LowerGap := ⟨vg, by omega⟩
      refine ⟨h, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [h] using hig
      · simpa [h] using hgj
      · simpa [v, a] using hav
      · simpa [v, b] using hvb
      · have hlofin : lowerGapLo h = natToFin2025 hg := by
          apply Fin.ext
          simp [h, lowerGapLo, natToFin2025_val (by omega : hg < 2025)]
        have hhifin : lowerGapHi h = natToFin2025 (hg + 1) := by
          apply Fin.ext
          simp [h, lowerGapHi, natToFin2025_val (by omega : hg + 1 < 2025)]
        rw [hlofin, hhifin]
        change min (row hg) (row (hg + 1)) ≤ vg ∧
          vg < max (row hg) (row (hg + 1))
        dsimp [a, b] at hglow hghigh hav hvb
        omega
      · have vlofin : lowerGapLo v = natToFin2025 vg := by
          apply Fin.ext
          simp [v, lowerGapLo, natToFin2025_val (by omega : vg < 2025)]
        have vhifin : lowerGapHi v = natToFin2025 (vg + 1) := by
          apply Fin.ext
          simp [v, lowerGapHi, natToFin2025_val (by omega : vg + 1 < 2025)]
        rw [vlofin, vhifin]
        change min (col vg) (col (vg + 1)) ≤ hg ∧
          hg < max (col vg) (col (vg + 1))
        omega
    · have hreverse : (σ j).val < (σ i).val := by omega
      have hrowEnds : b ≤ row i.val ∧ row j.val ≤ a := by
        rw [hrowi, hrowj]
        dsimp [a, b]
        omega
      obtain ⟨hg, hig, hgj, hghigh, hglow⟩ :=
        adjacent_high_low hij hrowEnds.1 hrowEnds.2 hrowOutside
      have hcolEnds : j.val ≤ col a ∧ col b ≤ i.val := by
        constructor
        · rcases hcoli with hai | haj
          · exfalso
            have haeq : a = (σ j).val := by dsimp [a]; omega
            have hcolaj : col a = j.val := by
              have halt : a < 2025 := by rw [haeq]; exact (σ j).isLt
              have hafin : natToFin2025 a = σ j := by
                apply Fin.ext
                rw [natToFin2025_val halt, haeq]
              simp [col, hafin]
            omega
          · omega
        · rcases hcolb with hbi | hbj
          · omega
          · exfalso
            have hbeq : b = (σ i).val := by dsimp [b]; omega
            have hcolbi : col b = i.val := by
              have hblt : b < 2025 := by rw [hbeq]; exact (σ i).isLt
              have hbfin : natToFin2025 b = σ i := by
                apply Fin.ext
                rw [natToFin2025_val hblt, hbeq]
              simp [col, hbfin]
            omega
      obtain ⟨vg, hav, hvb, hvhigh, hvlow⟩ :=
        adjacent_high_low hab hcolEnds.1 hcolEnds.2 hcolOutside
      let h : LowerGap := ⟨hg, by omega⟩
      let v : LowerGap := ⟨vg, by omega⟩
      refine ⟨h, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [h] using hig
      · simpa [h] using hgj
      · simpa [v, a] using hav
      · simpa [v, b] using hvb
      · have hlofin : lowerGapLo h = natToFin2025 hg := by
          apply Fin.ext
          simp [h, lowerGapLo, natToFin2025_val (by omega : hg < 2025)]
        have hhifin : lowerGapHi h = natToFin2025 (hg + 1) := by
          apply Fin.ext
          simp [h, lowerGapHi, natToFin2025_val (by omega : hg + 1 < 2025)]
        rw [hlofin, hhifin]
        change min (row hg) (row (hg + 1)) ≤ vg ∧
          vg < max (row hg) (row (hg + 1))
        dsimp [a, b] at hglow hghigh hav hvb
        omega
      · have vlofin : lowerGapLo v = natToFin2025 vg := by
          apply Fin.ext
          simp [v, lowerGapLo, natToFin2025_val (by omega : vg < 2025)]
        have vhifin : lowerGapHi v = natToFin2025 (vg + 1) := by
          apply Fin.ext
          simp [v, lowerGapHi, natToFin2025_val (by omega : vg + 1 < 2025)]
        rw [vlofin, vhifin]
        change min (col vg) (col (vg + 1)) ≤ hg ∧
          hg < max (col vg) (col (vg + 1))
        omega
termination_by j.val - i.val

private def TangentCompatible (σ : Equiv.Perm (Fin 2025))
    (H V : Finset LowerGap) : Prop :=
  ∀ h ∈ H, ∀ v ∈ V,
    ¬(CrossesCut (σ (lowerGapLo h)) (σ (lowerGapHi h)) v ∧
      CrossesCut (σ.symm (lowerGapLo v)) (σ.symm (lowerGapHi v)) h)

private lemma compatible_block_map_injective (σ : Equiv.Perm (Fin 2025))
    (H V : Finset LowerGap) (hcompat : TangentCompatible σ H V) :
    Function.Injective (fun i : Fin 2025 => (blockOf H i, blockOf V (σ i))) := by
  intro i j heq
  have hHblock : blockOf H i = blockOf H j := congrArg Prod.fst heq
  have hVblock : blockOf V (σ i) = blockOf V (σ j) := congrArg Prod.snd heq
  by_contra hij
  have hvalne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hvalne with hijlt | hjilt
  · obtain ⟨h, v, hih, hhj, hvlo, hvhi, hcrossRow, hcrossCol⟩ :=
      permutation_discrete_crossing σ i j hijlt
    have hhmem : h ∈ H := (blockOf_eq_iff H i j).1 hHblock h
      (by rw [min_eq_left hijlt.le]; exact hih)
      (by rw [max_eq_right hijlt.le]; exact hhj)
    have hvmem : v ∈ V := (blockOf_eq_iff V (σ i) (σ j)).1 hVblock v hvlo hvhi
    exact hcompat h hhmem v hvmem ⟨hcrossRow, hcrossCol⟩
  · obtain ⟨h, v, hjh, hhi, hvlo, hvhi, hcrossRow, hcrossCol⟩ :=
      permutation_discrete_crossing σ j i hjilt
    have hhmem : h ∈ H := (blockOf_eq_iff H i j).1 hHblock h
      (by rw [min_eq_right hjilt.le]; exact hjh)
      (by rw [max_eq_left hjilt.le]; exact hhi)
    have hvmem : v ∈ V := (blockOf_eq_iff V (σ i) (σ j)).1 hVblock v
      (by simpa [min_comm] using hvlo) (by simpa [max_comm] using hvhi)
    exact hcompat h hhmem v hvmem ⟨hcrossRow, hcrossCol⟩

private lemma compatible_block_product (σ : Equiv.Perm (Fin 2025))
    (H V : Finset LowerGap) (hcompat : TangentCompatible σ H V) :
    2025 ≤ (2025 - H.card) * (2025 - V.card) := by
  let f : Fin 2025 → Fin (2025 - H.card) × Fin (2025 - V.card) :=
    fun i => (blockOf H i, blockOf V (σ i))
  have hinj : Function.Injective f := compatible_block_map_injective σ H V hcompat
  have hcard := Fintype.card_le_of_injective f hinj
  simpa [f] using hcard

private lemma compatible_tangent_card_bound (σ : Equiv.Perm (Fin 2025))
    (H V : Finset LowerGap) (hcompat : TangentCompatible σ H V) :
    H.card + V.card ≤ 3960 := by
  have hH : H.card ≤ 2024 := by simpa using H.card_le_univ
  have hV : V.card ≤ 2024 := by simpa using V.card_le_univ
  exact compatible_card_upper_bound (compatible_block_product σ H V hcompat)

/-! ### Bridges between the seam, tangent-run, and block libraries -/

private lemma tangentBlackPermutation_eq_blackPermutationEquiv
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    tangentBlackPermutation hvalid = blackPermutationEquiv hvalid := by
  apply Equiv.ext
  intro x
  have hp : ((tangentBlackColumnEquiv hvalid).symm x).1 =
      (blackAtColumn hvalid x).1 := by
    apply hvalid.2.1
      ((tangentBlackColumnEquiv hvalid).symm x).1
      ((tangentBlackColumnEquiv hvalid).symm x).2
      (blackAtColumn hvalid x).1 (blackAtColumn_mem hvalid x)
    have htx : ((tangentBlackColumnEquiv hvalid).symm x).1.1 = x :=
      (tangentBlackColumnEquiv hvalid).apply_symm_apply x
    change ((tangentBlackColumnEquiv hvalid).symm x).1.1.val =
      (blackAtColumn hvalid x).1.1.val
    rw [htx, blackAtColumn_x hvalid x]
  exact congrArg Prod.snd hp

private def tangentPieceOwnerEquiv
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)} :
    TangentPiece all_black partition ≃ Owner all_black partition where
  toFun
    | Sum.inl m => Sum.inr m
    | Sum.inr b => Sum.inl b
  invFun
    | Sum.inl b => Sum.inr b
    | Sum.inr m => Sum.inl m
  left_inv := by
    intro o
    cases o <;> rfl
  right_inv := by
    intro o
    cases o <;> rfl

private lemma tangentPieceOwnerEquiv_owner
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (p : Point 2025) :
    tangentPieceOwnerEquiv (tangentPieceOwner hvalid.2.2.2 p) =
      configurationOwner all_black partition hvalid p := by
  by_cases hp : p ∈ all_black <;>
    simp [tangentPieceOwnerEquiv, tangentPieceOwner, configurationOwner, hp]

private lemma horizontalSeam_iff_IsHorizontalSeam
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (g : Gap) (x : Fin 2025) :
    horizontalSeam hvalid g x ↔
      IsHorizontalSeam (configurationOwner all_black partition hvalid) (x, g) := by
  let e : TangentPiece all_black partition ≃ Owner all_black partition :=
    tangentPieceOwnerEquiv
  change tangentPieceOwner hvalid.2.2.2 (x, gapLow g) ≠
      tangentPieceOwner hvalid.2.2.2 (x, gapHigh g) ↔
    configurationOwner all_black partition hvalid (x, gapLow g) ≠
      configurationOwner all_black partition hvalid (x, gapHigh g)
  rw [← tangentPieceOwnerEquiv_owner hvalid (x, gapLow g),
    ← tangentPieceOwnerEquiv_owner hvalid (x, gapHigh g)]
  exact e.injective.ne_iff.symm

private lemma verticalSeam_iff_IsVerticalSeam
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (g : Gap) (y : Fin 2025) :
    verticalSeam hvalid g y ↔
      IsVerticalSeam (configurationOwner all_black partition hvalid) (g, y) := by
  let e : TangentPiece all_black partition ≃ Owner all_black partition :=
    tangentPieceOwnerEquiv
  change tangentPieceOwner hvalid.2.2.2 (gapLow g, y) ≠
      tangentPieceOwner hvalid.2.2.2 (gapHigh g, y) ↔
    configurationOwner all_black partition hvalid (gapLow g, y) ≠
      configurationOwner all_black partition hvalid (gapHigh g, y)
  rw [← tangentPieceOwnerEquiv_owner hvalid (gapLow g, y),
    ← tangentPieceOwnerEquiv_owner hvalid (gapHigh g, y)]
  exact e.injective.ne_iff.symm

private lemma horizontal_tangent_supported_iff
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) :
    IsHorizontalTangentSupported hvalid g ↔
      IsRowTangentSupported (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid) g := by
  rw [← tangentBlackPermutation_eq_blackPermutationEquiv hvalid]
  let σ := tangentBlackPermutation hvalid
  let a := σ.symm (gapLow g)
  let b := σ.symm (gapHigh g)
  constructor
  · intro hs x hxlo hxhi
    apply (horizontalSeam_iff_IsHorizontalSeam hvalid g x).1
    by_cases hxa : x = a
    · subst x
      exact horizontalSeam_at_low_row_black hvalid g
    by_cases hxb : x = b
    · subst x
      exact horizontalSeam_at_high_row_black hvalid g
    apply hs x
    · have hxaVal : x.val ≠ a.val := fun h => hxa (Fin.ext h)
      have hxbVal : x.val ≠ b.val := fun h => hxb (Fin.ext h)
      change min a.val b.val + 1 - 1 ≤ x.val at hxlo
      change x.val ≤ max a.val b.val at hxhi
      change (lo a b).val < x.val
      simp only [Nat.add_sub_cancel] at hxlo
      simp only [lo]
      dsimp [a, b, σ] at hxlo hxhi hxaVal hxbVal ⊢
      omega
    · have hxaVal : x.val ≠ a.val := fun h => hxa (Fin.ext h)
      have hxbVal : x.val ≠ b.val := fun h => hxb (Fin.ext h)
      change min a.val b.val + 1 - 1 ≤ x.val at hxlo
      change x.val ≤ max a.val b.val at hxhi
      change x.val < (hi a b).val
      simp only [Nat.add_sub_cancel] at hxlo
      simp only [hi]
      dsimp [a, b, σ] at hxlo hxhi hxaVal hxbVal ⊢
      omega
  · intro hs x hxlo hxhi
    apply (horizontalSeam_iff_IsHorizontalSeam hvalid g x).2
    apply hs x
    · change min a.val b.val + 1 - 1 ≤ x.val
      change (lo a b).val < x.val at hxlo
      simp only [Nat.add_sub_cancel]
      simp only [lo] at hxlo
      dsimp [a, b, σ] at hxlo ⊢
      omega
    · change x.val ≤ max a.val b.val
      change x.val < (hi a b).val at hxhi
      simp only [hi] at hxhi
      dsimp [a, b, σ] at hxhi ⊢
      omega

private lemma vertical_tangent_supported_iff
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) (g : Gap) :
    IsVerticalTangentSupported hvalid g ↔
      IsColumnTangentSupported (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid) g := by
  rw [← tangentBlackPermutation_eq_blackPermutationEquiv hvalid]
  let σ := tangentBlackPermutation hvalid
  let a := σ (gapLow g)
  let b := σ (gapHigh g)
  constructor
  · intro hs y hylo hyhi
    apply (verticalSeam_iff_IsVerticalSeam hvalid g y).1
    by_cases hya : y = a
    · subst y
      exact verticalSeam_at_low_column_black hvalid g
    by_cases hyb : y = b
    · subst y
      exact verticalSeam_at_high_column_black hvalid g
    apply hs y
    · have hyaVal : y.val ≠ a.val := fun h => hya (Fin.ext h)
      have hybVal : y.val ≠ b.val := fun h => hyb (Fin.ext h)
      change min a.val b.val + 1 - 1 ≤ y.val at hylo
      change y.val ≤ max a.val b.val at hyhi
      change (lo a b).val < y.val
      simp only [Nat.add_sub_cancel] at hylo
      simp only [lo]
      dsimp [a, b, σ] at hylo hyhi hyaVal hybVal ⊢
      omega
    · have hyaVal : y.val ≠ a.val := fun h => hya (Fin.ext h)
      have hybVal : y.val ≠ b.val := fun h => hyb (Fin.ext h)
      change min a.val b.val + 1 - 1 ≤ y.val at hylo
      change y.val ≤ max a.val b.val at hyhi
      change y.val < (hi a b).val
      simp only [Nat.add_sub_cancel] at hylo
      simp only [hi]
      dsimp [a, b, σ] at hylo hyhi hyaVal hybVal ⊢
      omega
  · intro hs y hylo hyhi
    apply (verticalSeam_iff_IsVerticalSeam hvalid g y).2
    apply hs y
    · change min a.val b.val + 1 - 1 ≤ y.val
      change (lo a b).val < y.val at hylo
      simp only [Nat.add_sub_cancel]
      simp only [lo] at hylo
      dsimp [a, b, σ] at hylo ⊢
      omega
    · change y.val ≤ max a.val b.val
      change y.val < (hi a b).val at hyhi
      simp only [hi] at hyhi
      dsimp [a, b, σ] at hyhi ⊢
      omega

private lemma Ah_eq_supportedRowTangents
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Ah hvalid = supportedRowTangents
      (configurationOwner all_black partition hvalid)
      (blackPermutationEquiv hvalid) := by
  classical
  ext g
  simp only [Ah, supportedRowTangents, Finset.mem_filter, Finset.mem_univ, true_and]
  exact horizontal_tangent_supported_iff hvalid g

private lemma Av_eq_supportedColumnTangents
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    Av hvalid = supportedColumnTangents
      (configurationOwner all_black partition hvalid)
      (blackPermutationEquiv hvalid) := by
  classical
  ext g
  simp only [Av, supportedColumnTangents, Finset.mem_filter, Finset.mem_univ, true_and]
  exact vertical_tangent_supported_iff hvalid g

private lemma finiteSeamSequence_val_iff (seam : Fin 2025 → Prop) (x : Fin 2025) :
    finiteSeamSequence seam x.val ↔ seam x := by
  constructor
  · rintro ⟨hx, hs⟩
    have heq : (⟨x.val, hx⟩ : Fin 2025) = x := Fin.ext rfl
    simpa [heq] using hs
  · intro hs
    exact ⟨x.isLt, by simpa using hs⟩

private lemma horizontalGapRunStart_val_iff
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (g : Gap) (x : Fin 2025) :
    x.val ∈ horizontalGapRunStarts hvalid g ↔
      IsHorizontalRunStart (configurationOwner all_black partition hvalid) (x, g) := by
  classical
  rw [horizontalGapRunStarts, seamRunStarts,
    mem_tangentNatRunStarts (finiteSeamSequence (horizontalSeam hvalid g))]
  simp only [x.isLt, true_and, finiteSeamSequence_val_iff]
  constructor
  · rintro ⟨hseam, hzero | hprev⟩
    · exact ⟨(horizontalSeam_iff_IsHorizontalSeam hvalid g x).1 hseam,
        Or.inl hzero⟩
    · refine ⟨(horizontalSeam_iff_IsHorizontalSeam hvalid g x).1 hseam, ?_⟩
      by_cases hx0 : x.val = 0
      · exact Or.inl hx0
      · refine Or.inr ?_
        intro t htx htg ht
        apply hprev
        have hbound : x.val - 1 < 2025 := by omega
        refine ⟨hbound, ?_⟩
        have htx' : t.1.val + 1 = x.val := by simpa using htx
        have htg' : t.2 = g := by simpa using htg
        have htseam : horizontalSeam hvalid g t.1 := by
          apply (horizontalSeam_iff_IsHorizontalSeam hvalid g t.1).2
          rw [← htg']
          exact ht
        have heq : (⟨x.val - 1, hbound⟩ : Fin 2025) = t.1 := by
          apply Fin.ext
          change x.val - 1 = t.1.val
          omega
        simpa [heq] using htseam
  · rintro ⟨hseam, hzero | hprev⟩
    · exact ⟨(horizontalSeam_iff_IsHorizontalSeam hvalid g x).2 hseam,
        Or.inl hzero⟩
    · refine ⟨(horizontalSeam_iff_IsHorizontalSeam hvalid g x).2 hseam, ?_⟩
      by_cases hx0 : x.val = 0
      · exact Or.inl hx0
      · refine Or.inr ?_
        rintro ⟨hbound, hpseam⟩
        let t : Fin 2025 × Fin 2024 := (⟨x.val - 1, hbound⟩, g)
        apply hprev t
        · dsimp [t]
          omega
        · rfl
        · apply (horizontalSeam_iff_IsHorizontalSeam hvalid g t.1).1
          simpa [t] using hpseam

private lemma verticalGapRunStart_val_iff
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    (g : Gap) (y : Fin 2025) :
    y.val ∈ verticalGapRunStarts hvalid g ↔
      IsVerticalRunStart (configurationOwner all_black partition hvalid) (g, y) := by
  classical
  rw [verticalGapRunStarts, seamRunStarts,
    mem_tangentNatRunStarts (finiteSeamSequence (verticalSeam hvalid g))]
  simp only [y.isLt, true_and, finiteSeamSequence_val_iff]
  constructor
  · rintro ⟨hseam, hzero | hprev⟩
    · exact ⟨(verticalSeam_iff_IsVerticalSeam hvalid g y).1 hseam,
        Or.inl hzero⟩
    · refine ⟨(verticalSeam_iff_IsVerticalSeam hvalid g y).1 hseam, ?_⟩
      by_cases hy0 : y.val = 0
      · exact Or.inl hy0
      · refine Or.inr ?_
        intro t htg hty ht
        apply hprev
        have hbound : y.val - 1 < 2025 := by omega
        refine ⟨hbound, ?_⟩
        have htg' : t.1 = g := by simpa using htg
        have hty' : t.2.val + 1 = y.val := by simpa using hty
        have htseam : verticalSeam hvalid g t.2 := by
          apply (verticalSeam_iff_IsVerticalSeam hvalid g t.2).2
          rw [← htg']
          exact ht
        have heq : (⟨y.val - 1, hbound⟩ : Fin 2025) = t.2 := by
          apply Fin.ext
          change y.val - 1 = t.2.val
          omega
        simpa [heq] using htseam
  · rintro ⟨hseam, hzero | hprev⟩
    · exact ⟨(verticalSeam_iff_IsVerticalSeam hvalid g y).2 hseam,
        Or.inl hzero⟩
    · refine ⟨(verticalSeam_iff_IsVerticalSeam hvalid g y).2 hseam, ?_⟩
      by_cases hy0 : y.val = 0
      · exact Or.inl hy0
      · refine Or.inr ?_
        rintro ⟨hbound, hpseam⟩
        let t : Fin 2024 × Fin 2025 := (g, ⟨y.val - 1, hbound⟩)
        apply hprev t
        · rfl
        · dsimp [t]
          omega
        · apply (verticalSeam_iff_IsVerticalSeam hvalid g t.2).1
          simpa [t] using hpseam

private lemma horizontalGapRunStart_lt
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    {g : Gap} {j : ℕ} (hj : j ∈ horizontalGapRunStarts hvalid g) : j < 2025 := by
  classical
  rw [horizontalGapRunStarts, seamRunStarts,
    mem_tangentNatRunStarts (finiteSeamSequence (horizontalSeam hvalid g))] at hj
  exact hj.1

private lemma verticalGapRunStart_lt
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition)
    {g : Gap} {j : ℕ} (hj : j ∈ verticalGapRunStarts hvalid g) : j < 2025 := by
  classical
  rw [verticalGapRunStarts, seamRunStarts,
    mem_tangentNatRunStarts (finiteSeamSequence (verticalSeam hvalid g))] at hj
  exact hj.1

private def horizontalRunsMembershipEquiv
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    {z : Σ _ : Gap, ℕ // z ∈ horizontalRuns hvalid} ≃
      {s : Fin 2025 × Fin 2024 // s ∈ horizontalRunStarts
        (configurationOwner all_black partition hvalid)} where
  toFun z := by
    classical
    have hj : z.1.2 ∈ horizontalGapRunStarts hvalid z.1.1 :=
      (Finset.mem_sigma.mp z.2).2
    let x : Fin 2025 := ⟨z.1.2, horizontalGapRunStart_lt hvalid hj⟩
    refine ⟨(x, z.1.1), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    exact (horizontalGapRunStart_val_iff hvalid z.1.1 x).1 (by simpa [x] using hj)
  invFun s := by
    classical
    refine ⟨⟨s.1.2, s.1.1.val⟩, ?_⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (horizontalGapRunStart_val_iff hvalid s.1.2 s.1.1).2
      (Finset.mem_filter.1 s.2).2
  left_inv := by
    rintro ⟨⟨g, j⟩, hj⟩
    rfl
  right_inv := by
    rintro ⟨⟨x, g⟩, hs⟩
    rfl

private def verticalRunsMembershipEquiv
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    {z : Σ _ : Gap, ℕ // z ∈ verticalRuns hvalid} ≃
      {s : Fin 2024 × Fin 2025 // s ∈ verticalRunStarts
        (configurationOwner all_black partition hvalid)} where
  toFun z := by
    classical
    have hj : z.1.2 ∈ verticalGapRunStarts hvalid z.1.1 :=
      (Finset.mem_sigma.mp z.2).2
    let y : Fin 2025 := ⟨z.1.2, verticalGapRunStart_lt hvalid hj⟩
    refine ⟨(z.1.1, y), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    exact (verticalGapRunStart_val_iff hvalid z.1.1 y).1 (by simpa [y] using hj)
  invFun s := by
    classical
    refine ⟨⟨s.1.1, s.1.2.val⟩, ?_⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (verticalGapRunStart_val_iff hvalid s.1.1 s.1.2).2
      (Finset.mem_filter.1 s.2).2
  left_inv := by
    rintro ⟨⟨g, j⟩, hj⟩
    rfl
  right_inv := by
    rintro ⟨⟨g, y⟩, hs⟩
    rfl

private lemma horizontalRuns_card_eq_horizontalRunStarts_card
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    (horizontalRuns hvalid).card =
      (horizontalRunStarts (configurationOwner all_black partition hvalid)).card := by
  classical
  have hcard := Fintype.card_congr (horizontalRunsMembershipEquiv hvalid)
  simpa only [Fintype.card_coe] using hcard

private lemma verticalRuns_card_eq_verticalRunStarts_card
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    (verticalRuns hvalid).card =
      (verticalRunStarts (configurationOwner all_black partition hvalid)).card := by
  classical
  have hcard := Fintype.card_congr (verticalRunsMembershipEquiv hvalid)
  simpa only [Fintype.card_coe] using hcard

private lemma tangentConflict_iff_crossesCuts
    (σ : Equiv.Perm (Fin 2025)) (h v : Fin 2024) :
    TangentConflict σ h v ↔
      CrossesCut (σ (lowerGapLo v)) (σ (lowerGapHi v)) h ∧
      CrossesCut (σ.symm (lowerGapLo h)) (σ.symm (lowerGapHi h)) v := by
  simp only [TangentConflict, rowTangentStart, rowTangentStop,
    columnTangentStart, columnTangentStop, CrossesCut,
    gapLower, gapUpper, lowerGapLo, lowerGapHi, Nat.add_sub_cancel]
  tauto

private lemma compatible_tangents_are_block_compatible {α : Type}
    (owner : Point 2025 → α) (σ : Equiv.Perm (Fin 2025)) :
    TangentCompatible σ (compatibleColumnTangents owner σ)
      (compatibleRowTangents owner σ) := by
  intro v hv h hh hcross
  apply compatible_tangents_no_conflict owner σ hh hv
  exact (tangentConflict_iff_crossesCuts σ h v).2 hcross

private lemma configuration_horizontal_supported_run_bound
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    4048 ≤ (horizontalRunStarts
      (configurationOwner all_black partition hvalid)).card +
      (supportedRowTangents
        (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid)).card := by
  calc
    4048 ≤ (horizontalRuns hvalid).card + (Ah hvalid).card :=
      horizontal_supported_run_count hvalid
    _ = _ := congrArg₂ (· + ·)
      (horizontalRuns_card_eq_horizontalRunStarts_card hvalid)
      (congrArg Finset.card (Ah_eq_supportedRowTangents hvalid))

private lemma configuration_vertical_supported_run_bound
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    4048 ≤ (verticalRunStarts
      (configurationOwner all_black partition hvalid)).card +
      (supportedColumnTangents
        (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid)).card := by
  calc
    4048 ≤ (verticalRuns hvalid).card + (Av hvalid).card :=
      vertical_supported_run_count hvalid
    _ = _ := congrArg₂ (· + ·)
      (verticalRuns_card_eq_verticalRunStarts_card hvalid)
      (congrArg Finset.card (Av_eq_supportedColumnTangents hvalid))

private lemma configuration_compatible_tangent_card_bound
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    (compatibleRowTangents
      (configurationOwner all_black partition hvalid)
      (blackPermutationEquiv hvalid)).card +
      (compatibleColumnTangents
        (configurationOwner all_black partition hvalid)
        (blackPermutationEquiv hvalid)).card ≤ 3960 := by
  let owner := configurationOwner all_black partition hvalid
  let σ := blackPermutationEquiv hvalid
  have hbound := compatible_tangent_card_bound σ
    (compatibleColumnTangents owner σ) (compatibleRowTangents owner σ)
    (compatible_tangents_are_block_compatible owner σ)
  simpa [Nat.add_comm] using hbound

private lemma configuration_lower_bound
    {all_black : Finset (Point 2025)}
    {partition : Finset (Matilda 2025 all_black)}
    (hvalid : IsValidConfiguration 2025 all_black partition) :
    2112 ≤ partition.card := by
  have hintermediate := configuration_intermediate_bound hvalid
    (configuration_horizontal_supported_run_bound hvalid)
    (configuration_vertical_supported_run_bound hvalid)
  exact final_lower_bound_arithmetic hintermediate
    (configuration_compatible_tangent_card_bound hvalid)

/-- The minimum number of rectangles is attained by the 45-by-45 grid
construction and every valid configuration has at least that many rectangles. -/
theorem imo2025_p6 : IsMinMatildaCount 2025 solution_value := by
  constructor
  · intro all_black partition hvalid
    simpa [solution_value] using configuration_lower_bound hvalid
  · obtain ⟨all_black, partition, hvalid, hcard⟩ := grid_construction_upper_bound
    exact ⟨all_black, partition, hvalid, by simpa [solution_value] using hcard⟩

end IMO2025P6
