import Mathlib

namespace Imo2025P5

set_option autoImplicit false

/-- A finite position is valid when every move is nonnegative and every player-specific
constraint seen so far is satisfied. Indices are zero-based, so Alice moves at even
indices and Bazza at odd indices. -/
def ValidSeq (c : ℝ) {n : ℕ} (x : Fin n → ℝ) : Prop := (∀ i : Fin n, 0 ≤ x i) ∧
  (∀ i : Fin n, Even (i : ℕ) → (∑ j ≤ i, x j) ≤ c * ((i : ℕ) + 1)) ∧
  (∀ i : Fin n, Odd (i : ℕ) → (∑ j ≤ i, (x j) ^ 2) ≤ ((i : ℕ) + 1))

/-- Player `p` wins a finite play if the first invalid move was made by the other player. -/
def Wins (c : ℝ) (p : ℕ) {n : ℕ} (x : Fin n → ℝ) : Prop := ∃ i : Fin n, (i : ℕ) % 2 ≠ p ∧
  IsLeast {j : Fin n | ¬ ValidSeq c (Fin.take ((j : ℕ) + 1) (by omega) x)} i

abbrev Strategy : Type := ⦃k : ℕ⦄ → (Fin k → ℝ) → ℝ

def Strategy.play (s : Strategy) (p : ℕ) (opponentMoves : ℕ → ℝ) : (k : ℕ) → Fin k → ℝ
| 0 => Fin.elim0
| k + 1 => Fin.snoc (s.play p opponentMoves k)
    (if k % 2 = p then s (s.play p opponentMoves k) else opponentMoves k)

def Strategy.Winning (s : Strategy) (c : ℝ) (p : ℕ) : Prop :=
  ∀ opponentMoves : ℕ → ℝ, ∃ k : ℕ, Wins c p (s.play p opponentMoves k)

private lemma Strategy.play_succ (s : Strategy) (p : ℕ) (o : ℕ → ℝ) (k : ℕ) :
    s.play p o (k + 1) = Fin.snoc (s.play p o k)
      (if k % 2 = p then s (s.play p o k) else o k) := by
  rw [Strategy.play]

private lemma Strategy.play_apply (s : Strategy) (p : ℕ) (o : ℕ → ℝ)
    {n : ℕ} (i : Fin n) :
    s.play p o n i = if (i : ℕ) % 2 = p then s (s.play p o (i : ℕ)) else o i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => simp [Strategy.play]
    | cast j => simpa [Strategy.play] using ih j

private lemma Strategy.take_play (s : Strategy) (p : ℕ) (o : ℕ → ℝ)
    {n m : ℕ} (h : m ≤ n) :
    Fin.take m h (s.play p o n) = s.play p o m := by
  funext i
  simp only [Fin.take_apply, Strategy.play_apply]
  congr 1

/-- The exact two winning regions. At the boundary `1 / √2`, neither player has a
winning strategy. -/
abbrev answer : Set ℝ × Set ℝ :=
  (Set.Ioi (1 / Real.sqrt 2), Set.Iio (1 / Real.sqrt 2))

private lemma Iic_castSucc {k : ℕ} (i : Fin k) :
    Finset.Iic i.castSucc = (Finset.Iic i).map Fin.castSuccEmb := by
  ext j
  simp

private lemma sum_Iic_snoc_castSucc {k : ℕ} (x : Fin k → ℝ) (y : ℝ) (i : Fin k) :
    (∑ j ≤ i.castSucc, Fin.snoc x y j) = ∑ j ≤ i, x j := by
  rw [Iic_castSucc, Finset.sum_map]
  simp

private lemma sum_Iic_snoc_last {k : ℕ} (x : Fin k → ℝ) (y : ℝ) :
    (∑ j ≤ Fin.last k, Fin.snoc x y j) = (∑ j, x j) + y := by
  rw [← Fin.top_eq_last, Finset.Iic_top, Fin.sum_univ_castSucc]
  simp

private lemma sum_Iic_snoc_castSucc_sq {k : ℕ} (x : Fin k → ℝ) (y : ℝ) (i : Fin k) :
    (∑ j ≤ i.castSucc, (Fin.snoc x y j) ^ 2) = ∑ j ≤ i, (x j) ^ 2 := by
  rw [Iic_castSucc, Finset.sum_map]
  simp

private lemma sum_Iic_snoc_last_sq {k : ℕ} (x : Fin k → ℝ) (y : ℝ) :
    (∑ j ≤ Fin.last k, (Fin.snoc x y j) ^ 2) = (∑ j, (x j) ^ 2) + y ^ 2 := by
  rw [← Fin.top_eq_last, Finset.Iic_top, Fin.sum_univ_castSucc]
  simp

private lemma validSeq_snoc {c : ℝ} {k : ℕ} {x : Fin k → ℝ} {y : ℝ}
    (hx : ValidSeq c x) (hy : 0 ≤ y)
    (heven : Even k → (∑ i, x i) + y ≤ c * (k + 1))
    (hodd : Odd k → (∑ i, (x i) ^ 2) + y ^ 2 ≤ k + 1) :
    ValidSeq c (Fin.snoc x y) := by
  rcases hx with ⟨hx0, hxA, hxB⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simpa
    | cast j => simpa using hx0 j
  · intro i hi
    induction i using Fin.lastCases with
    | last => simpa [sum_Iic_snoc_last] using heven hi
    | cast j => simpa [sum_Iic_snoc_castSucc] using hxA j hi
  · intro i hi
    induction i using Fin.lastCases with
    | last => simpa [sum_Iic_snoc_last_sq] using hodd hi
    | cast j => simpa [sum_Iic_snoc_castSucc_sq] using hxB j hi

private lemma Iic_castLE {n m : ℕ} (h : m ≤ n) (i : Fin m) :
    Finset.Iic (Fin.castLE h i) = (Finset.Iic i).map (Fin.castLEEmb h) := by
  ext j
  simp

private lemma sum_Iic_take {n m : ℕ} (h : m ≤ n) (x : Fin n → ℝ) (i : Fin m) :
    (∑ j ≤ i, Fin.take m h x j) = ∑ j ≤ Fin.castLE h i, x j := by
  rw [Iic_castLE, Finset.sum_map]
  rfl

private lemma sum_Iic_take_sq {n m : ℕ} (h : m ≤ n) (x : Fin n → ℝ) (i : Fin m) :
    (∑ j ≤ i, (Fin.take m h x j) ^ 2) = ∑ j ≤ Fin.castLE h i, (x j) ^ 2 := by
  rw [Iic_castLE, Finset.sum_map]
  rfl

private lemma validSeq_take {c : ℝ} {n m : ℕ} (h : m ≤ n) {x : Fin n → ℝ}
    (hx : ValidSeq c x) : ValidSeq c (Fin.take m h x) := by
  rcases hx with ⟨hx0, hxA, hxB⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [Fin.take_apply] using hx0 (Fin.castLE h i)
  · intro i hi
    simpa only [sum_Iic_take] using hxA (Fin.castLE h i) hi
  · intro i hi
    simpa only [sum_Iic_take_sq] using hxB (Fin.castLE h i) hi

private lemma validSeq_sum_last {c : ℝ} {k : ℕ} {x : Fin (k + 1) → ℝ}
    (hx : ValidSeq c x) (hk : Even k) : (∑ i, x i) ≤ c * (k + 1) := by
  simpa [← Fin.top_eq_last, Finset.Iic_top] using hx.2.1 (Fin.last k) hk

private lemma validSeq_sq_last {c : ℝ} {k : ℕ} {x : Fin (k + 1) → ℝ}
    (hx : ValidSeq c x) (hk : Odd k) : (∑ i, (x i) ^ 2) ≤ k + 1 := by
  simpa [← Fin.top_eq_last, Finset.Iic_top] using hx.2.2 (Fin.last k) hk

private lemma even_eq_two_mul {n : ℕ} (h : Even n) : ∃ m, n = 2 * m := by
  rcases h with ⟨m, rfl⟩
  exact ⟨m, by omega⟩

private lemma odd_eq_two_mul_add_one {n : ℕ} (h : Odd n) : ∃ m, n = 2 * m + 1 := by
  rcases h with ⟨m, rfl⟩
  exact ⟨m, by omega⟩

private lemma wins_of_bad_and_self_legal {c : ℝ} {n p : ℕ} {x : Fin n → ℝ}
    (hbad : ∃ i : Fin n, ¬ ValidSeq c (Fin.take ((i : ℕ) + 1) (by omega) x))
    (hself : ∀ i : Fin n, (i : ℕ) % 2 = p →
      (∀ j : Fin n, j < i → ValidSeq c (Fin.take ((j : ℕ) + 1) (by omega) x)) →
      ValidSeq c (Fin.take ((i : ℕ) + 1) (by omega) x)) :
    Wins c p x := by
  classical
  let bad : Finset (Fin n) := Finset.univ.filter fun i =>
    ¬ ValidSeq c (Fin.take ((i : ℕ) + 1) (by omega) x)
  have hbad_ne : bad.Nonempty := by
    rcases hbad with ⟨i, hi⟩
    exact ⟨i, by simp [bad, hi]⟩
  let i := bad.min' hbad_ne
  refine ⟨i, ?_, ?_, ?_⟩
  · intro hip
    have hiBad : ¬ ValidSeq c (Fin.take ((i : ℕ) + 1) (by omega) x) := by
      simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using
        (Finset.min'_mem bad hbad_ne)
    apply hiBad
    apply hself i hip
    intro j hji
    by_contra hj
    have hjmem : j ∈ bad := by simp [bad, hj]
    exact (not_lt_of_ge (Finset.min'_le bad j hjmem)) hji
  · simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.min'_mem bad hbad_ne)
  · intro j hj
    have hjmem : j ∈ bad := by
      simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    exact Finset.min'_le bad j hjmem

private lemma not_wins_of_opponent_legal {c : ℝ} {n p : ℕ} {x : Fin n → ℝ}
    (hlegal : ∀ i : Fin n, (i : ℕ) % 2 ≠ p →
      (∀ j : Fin n, j < i → ValidSeq c (Fin.take ((j : ℕ) + 1) (by omega) x)) →
      ValidSeq c (Fin.take ((i : ℕ) + 1) (by omega) x)) :
    ¬ Wins c p x := by
  rintro ⟨i, hip, hiBad, hiLeast⟩
  apply hiBad
  apply hlegal i hip
  intro j hji
  by_contra hjBad
  exact (not_le_of_gt hji) (hiLeast hjBad)

private lemma wins_play_of_terminal_bad (s : Strategy) (c : ℝ) (p : ℕ) (o : ℕ → ℝ)
    {K : ℕ} (hbad : ¬ ValidSeq c (s.play p o (K + 1)))
    (hself : ∀ k ≤ K, k % 2 = p → ValidSeq c (s.play p o k) →
      ValidSeq c (s.play p o (k + 1))) : Wins c p (s.play p o (K + 1)) := by
  apply wins_of_bad_and_self_legal
  · refine ⟨Fin.last K, ?_⟩
    simpa only [Strategy.take_play]
  · intro i hip hprev
    simp only [Strategy.take_play]
    apply hself (i : ℕ) (Nat.le_of_lt_succ i.isLt) hip
    by_cases hi : (i : ℕ) = 0
    · refine ⟨?_, ?_, ?_⟩ <;> intro q
      all_goals have hq : (q : ℕ) < (i : ℕ) := q.isLt
      all_goals omega
    · let j : Fin (K + 1) := ⟨(i : ℕ) - 1,
        lt_trans (Nat.sub_lt (Nat.pos_of_ne_zero hi) Nat.one_pos) i.isLt⟩
      have hji : j < i :=
        Fin.mk_lt_mk.mpr (Nat.sub_lt (Nat.pos_of_ne_zero hi) Nat.one_pos)
      have hj := hprev j hji
      rw [Strategy.take_play] at hj
      have hji1 : (j : ℕ) + 1 = (i : ℕ) := Nat.sub_one_add_one hi
      rwa [hji1] at hj

private lemma cauchy_fin {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, x i) ^ 2 ≤ n * ∑ i, (x i) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun _ => (1 : ℝ))
  simpa [Finset.card_fin, mul_comm] using h

private lemma sum_le_m_sqrt_two {m : ℕ} {a q : ℝ} (ha : 0 ≤ a)
    (hcs : a ^ 2 ≤ m * q) (hq : q ≤ 2 * m) : a ≤ m * Real.sqrt 2 := by
  have hs0 : 0 ≤ (m : ℝ) * Real.sqrt 2 :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ ha hs0).mp
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hm : 0 ≤ (m : ℝ) := by positivity
  calc
    a ^ 2 ≤ (m : ℝ) * q := hcs
    _ ≤ (m : ℝ) * (2 * m) := mul_le_mul_of_nonneg_left hq hm
    _ = ((m : ℝ) * Real.sqrt 2) ^ 2 := by rw [mul_pow, hs2]; ring

private lemma sqrt_two_pos : 0 < Real.sqrt 2 := by positivity

private lemma inv_sqrt_two_eq : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by positivity)
  field_simp
  nlinarith

private noncomputable def fill (a : ℝ) : ℝ := Real.sqrt (2 - a ^ 2)

private lemma fill_nonneg (a : ℝ) : 0 ≤ fill a := Real.sqrt_nonneg _

private lemma pair_sq_fill {a : ℝ} (ha : a ^ 2 ≤ 2) :
    a ^ 2 + (fill a) ^ 2 = 2 := by
  rw [show (fill a) ^ 2 = 2 - a ^ 2 by exact Real.sq_sqrt (by linarith)]
  ring

private lemma pair_sum_fill {a : ℝ} (ha0 : 0 ≤ a) (ha : a ^ 2 ≤ 2) :
    Real.sqrt 2 ≤ a + fill a := by
  have hf0 : 0 ≤ fill a := fill_nonneg a
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  apply (sq_le_sq₀ hs0 (add_nonneg ha0 hf0)).mp
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  calc
    (2 : ℝ) = a ^ 2 + (fill a) ^ 2 := (pair_sq_fill ha).symm
    _ ≤ (a + fill a) ^ 2 := by nlinarith [mul_nonneg ha0 hf0]

private lemma choose_bazza_time (c : ℝ) (hc : c < 1 / Real.sqrt 2) :
    ∃ N : ℕ, c * (2 * N + 1) < N * Real.sqrt 2 := by
  have hd : 0 < Real.sqrt 2 - 2 * c := by
    rw [inv_sqrt_two_eq] at hc
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (c / (Real.sqrt 2 - 2 * c))
  refine ⟨N + 1, ?_⟩
  have hm := (div_lt_iff₀ hd).mp hN
  push_cast at hm ⊢
  nlinarith

private lemma choose_spike_time (c : ℝ) (hc : 1 / Real.sqrt 2 < c) :
    ∃ N : ℕ, 2 * N + 2 < (c * (2 * N + 1) - N * Real.sqrt 2) ^ 2 := by
  have hd : 0 < 2 * c - Real.sqrt 2 := by
    rw [inv_sqrt_two_eq] at hc
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((3 : ℝ) / (2 * c - Real.sqrt 2) ^ 2)
  refine ⟨N + 1, ?_⟩
  have hd2 : 0 < (2 * c - Real.sqrt 2) ^ 2 := sq_pos_of_pos hd
  have hm := (div_lt_iff₀ hd2).mp hN
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by positivity)
  push_cast at hm ⊢
  nlinarith [mul_pos hd (show 0 < (N : ℝ) + 1 by positivity), sq_nonneg c]

/-- The all-zero strategy is the counterstrategy at and above the threshold. -/
private def aliceZero : Strategy := fun _ => 0

private lemma aliceZero_play_sum (o : ℕ → ℝ) : ∀ m,
    (∑ i, aliceZero.play 0 o (2 * m) i) = ∑ r : Fin m, o (2 * (r : ℕ) + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Nat.mul_succ]
    rw [Strategy.play_succ, Strategy.play_succ]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp [aliceZero, ih]

private lemma aliceZero_play_sq_sum (o : ℕ → ℝ) : ∀ m,
    (∑ i, (aliceZero.play 0 o (2 * m) i) ^ 2) =
      ∑ r : Fin m, (o (2 * (r : ℕ) + 1)) ^ 2 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Nat.mul_succ]
    rw [Strategy.play_succ, Strategy.play_succ]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp [aliceZero, ih]

private lemma aliceZero_sum_bound {c : ℝ} (o : ℕ → ℝ) {m : ℕ}
    (hx : ValidSeq c (aliceZero.play 0 o (2 * m))) :
    (∑ i, aliceZero.play 0 o (2 * m) i) ≤ m * Real.sqrt 2 := by
  have hnonneg : 0 ≤ ∑ i, aliceZero.play 0 o (2 * m) i :=
    Finset.sum_nonneg fun i _ => hx.1 i
  have hsq : (∑ i, (aliceZero.play 0 o (2 * m) i) ^ 2) ≤ 2 * m := by
    by_cases hm : m = 0
    · subst m
      simp
    · have hodd : Odd (2 * m - 1) := by
        rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega]
        exact ⟨m - 1, by omega⟩
      have htake := validSeq_take (c := c) (show 2 * m - 1 + 1 ≤ 2 * m by omega) hx
      have hprefix : ValidSeq c (aliceZero.play 0 o (2 * m - 1 + 1)) := by
        simpa only [Strategy.take_play] using htake
      have heq : 2 * m - 1 + 1 = 2 * m := by omega
      have hb := validSeq_sq_last (c := c) (k := 2 * m - 1) hprefix hodd
      have hcast : (((2 * m - 1 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) := by
        norm_num only [Nat.cast_sub (by omega : 1 ≤ 2 * m), Nat.cast_mul, Nat.cast_ofNat]
        ring
      rw [hcast] at hb
      rw [← heq]
      exact hb
  rw [aliceZero_play_sum] at hnonneg ⊢
  rw [aliceZero_play_sq_sum] at hsq
  exact sum_le_m_sqrt_two hnonneg (cauchy_fin fun r : Fin m => o (2 * (r : ℕ) + 1)) hsq

/-- Alice waits for a fixed number of her turns, then spends all of her accumulated
linear allowance in one move. -/
private def aliceSpike (c : ℝ) (N : ℕ) : Strategy := fun {k} x =>
  if k = 2 * N then c * (k + 1) - ∑ i, x i else 0

private lemma aliceSpike_prefix_eq_zero (c : ℝ) (N k : ℕ) (hk : k ≤ 2 * N)
    (o : ℕ → ℝ) : (aliceSpike c N).play 0 o k = aliceZero.play 0 o k := by
  funext i
  simp only [Strategy.play_apply]
  by_cases he : (i : ℕ) % 2 = 0
  · simp only [he, ↓reduceIte, aliceSpike, aliceZero]
    split_ifs with h
    · have hi := i.isLt
      omega
    · rfl
  · simp only [he, ↓reduceIte]

/-- Bazza fills the remaining square budget of the current pair. -/
private noncomputable def bazzaFill : Strategy := fun {k} x =>
  if h : k = 0 then 0
  else Real.sqrt (2 - (x ⟨k - 1, Nat.sub_lt (Nat.zero_lt_of_ne_zero h) Nat.one_pos⟩) ^ 2)

private lemma bazzaFill_at_odd {m : ℕ} (x : Fin (2 * m + 1) → ℝ) :
    bazzaFill x = fill (x (Fin.last (2 * m))) := by
  unfold bazzaFill fill
  simp only [show 2 * m + 1 ≠ 0 by omega, ↓reduceDIte]
  congr 2

private lemma bazzaFill_play_pair (o : ℕ → ℝ) (m : ℕ) :
    bazzaFill.play 1 o (2 * (m + 1)) =
      Fin.snoc (Fin.snoc (bazzaFill.play 1 o (2 * m)) (o (2 * m)))
        (fill (o (2 * m))) := by
  simp only [Nat.mul_succ]
  rw [Strategy.play_succ, Strategy.play_succ]
  have he : (2 * m) % 2 ≠ 1 := by omega
  have ho : (2 * m + 1) % 2 = 1 := by omega
  simp only [he, ho, ↓reduceIte]
  rw [bazzaFill_at_odd]
  simp

private lemma sum_snoc_snoc {n : ℕ} (x : Fin n → ℝ) (a b : ℝ) :
    (∑ i, Fin.snoc (Fin.snoc x a) b i) = (∑ i, x i) + a + b := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp

private lemma sum_snoc_snoc_sq {n : ℕ} (x : Fin n → ℝ) (a b : ℝ) :
    (∑ i, (Fin.snoc (Fin.snoc x a) b i) ^ 2) =
      (∑ i, (x i) ^ 2) + a ^ 2 + b ^ 2 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp

private def duel (alice bazza : Strategy) : (k : ℕ) → Fin k → ℝ
| 0 => Fin.elim0
| k + 1 => Fin.snoc (duel alice bazza k)
    (if k % 2 = 0 then alice (duel alice bazza k) else bazza (duel alice bazza k))

private lemma play_alice_eq_duel (alice bazza : Strategy) :
    ∀ k, alice.play 0 (fun m => bazza (duel alice bazza m)) k = duel alice bazza k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [Strategy.play, duel, ih]

private lemma play_bazza_eq_duel (alice bazza : Strategy) :
    ∀ k, bazza.play 1 (fun m => alice (duel alice bazza m)) k = duel alice bazza k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Strategy.play, duel, ih]
    congr 1
    by_cases h0 : k % 2 = 0
    · simp [h0]
    · have h1 : k % 2 = 1 := Nat.mod_two_ne_zero.mp h0
      simp [h1]

private lemma bazza_history {c : ℝ} (hc : c ≤ 1 / Real.sqrt 2) (o : ℕ → ℝ) : ∀ m,
    ValidSeq c (bazzaFill.play 1 o (2 * m + 1)) →
      (∑ i, (bazzaFill.play 1 o (2 * m) i) ^ 2) = 2 * m ∧
      (m : ℝ) * Real.sqrt 2 ≤ ∑ i, bazzaFill.play 1 o (2 * m) i ∧
      0 ≤ o (2 * m) ∧ (o (2 * m)) ^ 2 ≤ 2 := by
  intro m
  induction m with
  | zero =>
    intro hx
    have ha0 : 0 ≤ o 0 := by
      simpa [Strategy.play] using hx.1 (Fin.last 0)
    have ha_le : o 0 ≤ c := by
      simpa [Strategy.play] using validSeq_sum_last hx (show Even 0 by simp)
    have hc_sqrt : c < Real.sqrt 2 := by
      rw [inv_sqrt_two_eq] at hc
      have hs : 0 < Real.sqrt 2 := sqrt_two_pos
      linarith
    refine ⟨by simp, by simp, ha0, ?_⟩
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by positivity)
    nlinarith
  | succ m ih =>
    intro hx
    have hxprev : ValidSeq c (bazzaFill.play 1 o (2 * m + 1)) := by
      have htake := validSeq_take (c := c) (show 2 * m + 1 ≤ 2 * (m + 1) + 1 by omega) hx
      simpa only [Strategy.take_play] using htake
    rcases ih hxprev with ⟨hsq, hsum, ha0, ha2⟩
    have hsq' : (∑ i, (bazzaFill.play 1 o (2 * (m + 1)) i) ^ 2) = 2 * (m + 1) := by
      calc
        (∑ i, (bazzaFill.play 1 o (2 * (m + 1)) i) ^ 2) =
            (∑ i, (bazzaFill.play 1 o (2 * m) i) ^ 2) +
              (o (2 * m)) ^ 2 + (fill (o (2 * m))) ^ 2 := by
          rw [bazzaFill_play_pair]
          exact sum_snoc_snoc_sq _ _ _
        _ = 2 * (m + 1) := by
          rw [hsq]
          nlinarith [pair_sq_fill ha2]
    have hsum' : ((m + 1 : ℕ) : ℝ) * Real.sqrt 2 ≤
        ∑ i, bazzaFill.play 1 o (2 * (m + 1)) i := by
      calc
        ((m + 1 : ℕ) : ℝ) * Real.sqrt 2 =
            (m : ℝ) * Real.sqrt 2 + Real.sqrt 2 := by push_cast; ring
        _ ≤ (∑ i, bazzaFill.play 1 o (2 * m) i) +
            (o (2 * m) + fill (o (2 * m))) :=
          add_le_add hsum (pair_sum_fill ha0 ha2)
        _ = ∑ i, bazzaFill.play 1 o (2 * (m + 1)) i := by
          have hsum_pair :=
            sum_snoc_snoc (bazzaFill.play 1 o (2 * m)) (o (2 * m)) (fill (o (2 * m)))
          rw [bazzaFill_play_pair]
          calc
            (∑ i, bazzaFill.play 1 o (2 * m) i) +
                (o (2 * m) + fill (o (2 * m))) =
              (∑ i, bazzaFill.play 1 o (2 * m) i) +
                o (2 * m) + fill (o (2 * m)) := by ring
            _ = _ := hsum_pair.symm
    have hb0 : 0 ≤ o (2 * (m + 1)) := by
      simpa [Strategy.play] using hx.1 (Fin.last (2 * (m + 1)))
    have htotal : (∑ i, bazzaFill.play 1 o (2 * (m + 1)) i) +
        o (2 * (m + 1)) ≤ c * (2 * (m + 1) + 1) := by
      simpa [Strategy.play, Fin.sum_univ_castSucc] using
        validSeq_sum_last hx (show Even (2 * (m + 1)) by exact ⟨m + 1, by omega⟩)
    have hc' : c ≤ Real.sqrt 2 / 2 := by rw [← inv_sqrt_two_eq]; exact hc
    have hb_lt : o (2 * (m + 1)) < Real.sqrt 2 := by
      have hs : 0 < Real.sqrt 2 := sqrt_two_pos
      push_cast at htotal hsum' ⊢
      nlinarith
    have hb2 : (o (2 * (m + 1))) ^ 2 ≤ 2 := by
      have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by positivity)
      nlinarith
    exact ⟨by simpa using hsq', hsum', hb0, hb2⟩

private lemma bazza_wins_of_lt {c : ℝ} (hc : c < 1 / Real.sqrt 2) :
    ∃ s : Strategy, s.Winning c 1 := by
  refine ⟨bazzaFill, ?_⟩
  intro o
  obtain ⟨N, hN⟩ := choose_bazza_time c hc
  refine ⟨2 * N + 1, ?_⟩
  apply wins_play_of_terminal_bad
  · intro hx
    rcases bazza_history (le_of_lt hc) o N hx with ⟨_, hsum, _, _⟩
    have htotal := validSeq_sum_last hx (show Even (2 * N) by exact ⟨N, by omega⟩)
    have hlast : o (2 * N) = bazzaFill.play 1 o (2 * N + 1) (Fin.last (2 * N)) := by
      simp [Strategy.play]
    have hnonneg := hx.1 (Fin.last (2 * N))
    rw [← hlast] at hnonneg
    have hsum' : (∑ i, bazzaFill.play 1 o (2 * N) i) + o (2 * N) =
        ∑ i, bazzaFill.play 1 o (2 * N + 1) i := by
      rw [Strategy.play, Fin.sum_univ_castSucc]
      simp
    rw [← hsum'] at htotal
    push_cast at htotal hsum hN
    linarith
  · intro k hk hmod hx
    have hodd : Odd k := Nat.odd_iff.mpr hmod
    obtain ⟨m, rfl⟩ := odd_eq_two_mul_add_one hodd
    rcases bazza_history (le_of_lt hc) o m hx with ⟨hsq, _, ha0, ha2⟩
    rw [Strategy.play]
    simp only [hmod, ↓reduceIte, bazzaFill_at_odd]
    apply validSeq_snoc hx (fill_nonneg _)
    · intro he
      exfalso
      exact (Nat.not_even_iff_odd.mpr hodd) he
    · intro _
      have hlast : bazzaFill.play 1 o (2 * m + 1) (Fin.last (2 * m)) = o (2 * m) := by
        simp [Strategy.play]
      have hsqodd : (∑ i, (bazzaFill.play 1 o (2 * m + 1) i) ^ 2) =
          (∑ i, (bazzaFill.play 1 o (2 * m) i) ^ 2) + (o (2 * m)) ^ 2 := by
        rw [Strategy.play, Fin.sum_univ_castSucc]
        simp
      rw [hlast, hsqodd, hsq]
      push_cast
      nlinarith [pair_sq_fill ha2]

private lemma alice_wins_of_lt {c : ℝ} (hc : 1 / Real.sqrt 2 < c) :
    ∃ s : Strategy, s.Winning c 0 := by
  obtain ⟨N, hspike⟩ := choose_spike_time c hc
  refine ⟨aliceSpike c N, ?_⟩
  intro o
  refine ⟨2 * N + 2, ?_⟩
  apply wins_play_of_terminal_bad
  · intro hx
    have hbefore := validSeq_take (c := c) (show 2 * N ≤ 2 * N + 2 by omega) hx
    rw [Strategy.take_play, aliceSpike_prefix_eq_zero c N (2 * N) (by omega)] at hbefore
    have hsum := aliceZero_sum_bound o hbefore
    have hlast : (aliceSpike c N).play 0 o (2 * N + 1) (Fin.last (2 * N)) =
        c * (2 * N + 1) - ∑ i, aliceZero.play 0 o (2 * N) i := by
      rw [Strategy.play]
      simp only [show (2 * N) % 2 = 0 by omega, ↓reduceIte, aliceSpike]
      rw [aliceSpike_prefix_eq_zero c N (2 * N) (by omega)]
      norm_num
    have hsqprefix : ((aliceSpike c N).play 0 o (2 * N + 1) (Fin.last (2 * N))) ^ 2 ≤
        2 * N + 2 := by
      have htotal := validSeq_sq_last (c := c) (k := 2 * N + 1) hx
        (show Odd (2 * N + 1) by exact ⟨N, by omega⟩)
      let idx : Fin (2 * N + 2) := ⟨2 * N, by omega⟩
      have hsingle := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun i => ((aliceSpike c N).play 0 o (2 * N + 2) i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ idx)
      have hprefix_last : (aliceSpike c N).play 0 o (2 * N + 2) idx =
          (aliceSpike c N).play 0 o (2 * N + 1) (Fin.last (2 * N)) := by
        simp only [Strategy.play_apply, idx]
        congr 1
      change ((aliceSpike c N).play 0 o (2 * N + 2) idx) ^ 2 ≤ _ at hsingle
      rw [hprefix_last] at hsingle
      push_cast at htotal ⊢
      linarith
    have hspike_lower : N * Real.sqrt 2 < c * (2 * N + 1) := by
      rw [inv_sqrt_two_eq] at hc
      have hs : 0 < Real.sqrt 2 := sqrt_two_pos
      nlinarith
    have hspike_nonneg : 0 ≤ c * (2 * N + 1) -
        ∑ i, aliceZero.play 0 o (2 * N) i := by
      push_cast at hsum hspike_lower ⊢
      linarith
    have hspike_sq : (c * (2 * N + 1) -
        ∑ i, aliceZero.play 0 o (2 * N) i) ^ 2 > 2 * N + 2 := by
      have hbase0 : 0 ≤ c * (2 * N + 1) - N * Real.sqrt 2 := le_of_lt (by
        linarith)
      have hmono : c * (2 * N + 1) - N * Real.sqrt 2 ≤
          c * (2 * N + 1) - ∑ i, aliceZero.play 0 o (2 * N) i := by
        push_cast at hsum ⊢
        linarith
      have hsquares := sq_le_sq₀ hbase0 hspike_nonneg |>.mpr hmono
      push_cast at hspike hsquares ⊢
      linarith
    rw [hlast] at hsqprefix
    push_cast at hsqprefix hspike_sq
    linarith
  · intro k hk hmod hx
    have heven : Even k := Nat.even_iff.mpr hmod
    obtain ⟨m, rfl⟩ := even_eq_two_mul heven
    have hm : m ≤ N := by omega
    rw [Strategy.play]
    by_cases hEq : m = N
    · subst m
      simp only [show (2 * N) % 2 = 0 by omega, ↓reduceIte, aliceSpike]
      rw [aliceSpike_prefix_eq_zero c N (2 * N) (by omega)] at hx ⊢
      have hsum := aliceZero_sum_bound o hx
      have hspike_lower : N * Real.sqrt 2 < c * (2 * N + 1) := by
        rw [inv_sqrt_two_eq] at hc
        have hs : 0 < Real.sqrt 2 := sqrt_two_pos
        nlinarith
      have hmove0 : 0 ≤ c * ((2 * N : ℕ) + 1) -
          ∑ i, aliceZero.play 0 o (2 * N) i := by
        push_cast at hsum hspike_lower ⊢
        linarith
      apply validSeq_snoc hx hmove0
      · intro _
        push_cast
        ring_nf
        rfl
      · intro hodd
        exact False.elim ((Nat.not_even_iff_odd.mpr hodd) ⟨N, by omega⟩)
    · have hlt : 2 * m < 2 * N := by omega
      simp only [show (2 * m) % 2 = 0 by omega, ↓reduceIte, aliceSpike,
        show ¬2 * m = 2 * N by omega, ↓reduceIte]
      apply validSeq_snoc hx (by positivity)
      · intro _
        have hxzero : (aliceSpike c N).play 0 o (2 * m) = aliceZero.play 0 o (2 * m) :=
          aliceSpike_prefix_eq_zero c N (2 * m) (by omega) o
        rw [hxzero] at hx ⊢
        have hsum := aliceZero_sum_bound o hx
        rw [inv_sqrt_two_eq] at hc
        have hs : 0 < Real.sqrt 2 := sqrt_two_pos
        push_cast at hsum ⊢
        nlinarith
      · intro hodd
        exact False.elim ((Nat.not_even_iff_odd.mpr hodd) ⟨m, by omega⟩)

private lemma alice_not_winning_of_le {c : ℝ} (hc : c ≤ 1 / Real.sqrt 2) :
    ¬ ∃ s : Strategy, s.Winning c 0 := by
  rintro ⟨s, hs⟩
  let o : ℕ → ℝ := fun m => bazzaFill (duel s bazzaFill m)
  rcases hs o with ⟨k, hw⟩
  have hplay : s.play 0 o k = duel s bazzaFill k := play_alice_eq_duel s bazzaFill k
  rw [hplay] at hw
  have hcounter : bazzaFill.play 1 (fun m => s (duel s bazzaFill m)) k =
      duel s bazzaFill k := play_bazza_eq_duel s bazzaFill k
  apply not_wins_of_opponent_legal (c := c) (p := 0) (x := duel s bazzaFill k) (by
    intro i hi hprev
    have hi1 : (i : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hi
    have hodd : Odd (i : ℕ) := Nat.odd_iff.mpr hi1
    obtain ⟨m, hm⟩ := odd_eq_two_mul_add_one hodd
    have hduel_take : ∀ {r : ℕ} (hr : r ≤ k),
        Fin.take r hr (duel s bazzaFill k) = duel s bazzaFill r := by
      intro r hr
      calc
        Fin.take r hr (duel s bazzaFill k) =
            Fin.take r hr (bazzaFill.play 1 (fun m => s (duel s bazzaFill m)) k) := by
          rw [hcounter]
        _ = bazzaFill.play 1 (fun m => s (duel s bazzaFill m)) r :=
          Strategy.take_play bazzaFill 1 (fun m => s (duel s bazzaFill m)) hr
        _ = duel s bazzaFill r := play_bazza_eq_duel s bazzaFill r
    have hprefix : ValidSeq c (bazzaFill.play 1 (fun m => s (duel s bazzaFill m)) (i : ℕ)) := by
      by_cases hi0 : (i : ℕ) = 0
      · omega
      · let j : Fin k := ⟨(i : ℕ) - 1,
          lt_trans (Nat.sub_lt (Nat.pos_of_ne_zero hi0) Nat.one_pos) i.isLt⟩
        have hji : j < i :=
          Fin.mk_lt_mk.mpr (Nat.sub_lt (Nat.pos_of_ne_zero hi0) Nat.one_pos)
        have hj := hprev j hji
        rw [hduel_take (show (j : ℕ) + 1 ≤ k by omega)] at hj
        rw [← play_bazza_eq_duel s bazzaFill ((j : ℕ) + 1)] at hj
        have hji1 : (j : ℕ) + 1 = (i : ℕ) := Nat.sub_one_add_one hi0
        rwa [hji1] at hj
    have hprefix' : ValidSeq c (bazzaFill.play 1 (fun m => s (duel s bazzaFill m)) (2 * m + 1)) := by
      rw [hm] at hprefix
      exact hprefix
    rcases bazza_history hc (fun m => s (duel s bazzaFill m)) m hprefix' with
      ⟨hsq, _, ha0, ha2⟩
    rw [← hcounter]
    have htake_i := Strategy.take_play bazzaFill 1 (fun m => s (duel s bazzaFill m))
      (show (i : ℕ) + 1 ≤ k by omega)
    rw [htake_i]
    rw [Strategy.play]
    simp only [hi1, ↓reduceIte]
    rw [hm]
    simp only [bazzaFill_at_odd]
    have hlast : bazzaFill.play 1 (fun m => s (duel s bazzaFill m)) (2 * m + 1)
        (Fin.last (2 * m)) = s (duel s bazzaFill (2 * m)) := by
      simp [Strategy.play]
    rw [hlast]
    have hfill0 : 0 ≤ fill (s (duel s bazzaFill (2 * m))) := fill_nonneg _
    apply validSeq_snoc hprefix' hfill0
    · intro he
      exact False.elim ((Nat.not_even_iff_odd.mpr (show Odd (2 * m + 1) by exact ⟨m, by omega⟩)) he)
    · intro _
      have hsqodd :
          (∑ i, (bazzaFill.play 1 (fun m => s (duel s bazzaFill m)) (2 * m + 1) i) ^ 2) =
            (∑ i, (bazzaFill.play 1 (fun m => s (duel s bazzaFill m)) (2 * m) i) ^ 2) +
              (s (duel s bazzaFill (2 * m))) ^ 2 := by
        rw [Strategy.play, Fin.sum_univ_castSucc]
        simp
      rw [hsqodd, hsq]
      push_cast
      nlinarith [pair_sq_fill ha2]) hw

private lemma bazza_not_winning_of_le {c : ℝ} (hc : 1 / Real.sqrt 2 ≤ c) :
    ¬ ∃ s : Strategy, s.Winning c 1 := by
  rintro ⟨s, hs⟩
  let o : ℕ → ℝ := fun m => aliceZero (duel aliceZero s m)
  rcases hs o with ⟨k, hw⟩
  have hplay : s.play 1 o k = duel aliceZero s k := play_bazza_eq_duel aliceZero s k
  rw [hplay] at hw
  have hcounter : aliceZero.play 0 (fun m => s (duel aliceZero s m)) k =
      duel aliceZero s k := play_alice_eq_duel aliceZero s k
  apply not_wins_of_opponent_legal (c := c) (p := 1) (x := duel aliceZero s k) (by
    intro i hi hprev
    have hi0 : (i : ℕ) % 2 = 0 := Nat.mod_two_not_eq_one.mp hi
    have heven : Even (i : ℕ) := Nat.even_iff.mpr hi0
    obtain ⟨m, hm⟩ := even_eq_two_mul heven
    have hduel_take : ∀ {r : ℕ} (hr : r ≤ k),
        Fin.take r hr (duel aliceZero s k) = duel aliceZero s r := by
      intro r hr
      calc
        Fin.take r hr (duel aliceZero s k) =
            Fin.take r hr (aliceZero.play 0 (fun m => s (duel aliceZero s m)) k) := by
          rw [hcounter]
        _ = aliceZero.play 0 (fun m => s (duel aliceZero s m)) r :=
          Strategy.take_play aliceZero 0 (fun m => s (duel aliceZero s m)) hr
        _ = duel aliceZero s r := play_alice_eq_duel aliceZero s r
    have hprefix : ValidSeq c (aliceZero.play 0 (fun m => s (duel aliceZero s m)) (i : ℕ)) := by
      by_cases hiZero : (i : ℕ) = 0
      · refine ⟨?_, ?_, ?_⟩ <;> intro q
        all_goals have hq : (q : ℕ) < (i : ℕ) := q.isLt
        all_goals omega
      · let j : Fin k := ⟨(i : ℕ) - 1,
          lt_trans (Nat.sub_lt (Nat.pos_of_ne_zero hiZero) Nat.one_pos) i.isLt⟩
        have hji : j < i :=
          Fin.mk_lt_mk.mpr (Nat.sub_lt (Nat.pos_of_ne_zero hiZero) Nat.one_pos)
        have hj := hprev j hji
        rw [hduel_take (show (j : ℕ) + 1 ≤ k by omega)] at hj
        rw [← play_alice_eq_duel aliceZero s ((j : ℕ) + 1)] at hj
        have hji1 : (j : ℕ) + 1 = (i : ℕ) := Nat.sub_one_add_one hiZero
        rwa [hji1] at hj
    rw [← hcounter]
    have htake_i := Strategy.take_play aliceZero 0 (fun m => s (duel aliceZero s m))
      (show (i : ℕ) + 1 ≤ k by omega)
    rw [htake_i, Strategy.play]
    simp only [hi0, ↓reduceIte, aliceZero]
    apply validSeq_snoc hprefix (by norm_num)
    · intro _
      have hprefix' : ValidSeq c
          (aliceZero.play 0 (fun m => s (duel aliceZero s m)) (2 * m)) := by
        rw [← hm]
        exact hprefix
      have hsum := aliceZero_sum_bound (fun m => s (duel aliceZero s m)) hprefix'
      rw [hm]
      rw [inv_sqrt_two_eq] at hc
      have hthr : (m : ℝ) * Real.sqrt 2 ≤ c * (2 * m + 1) := by
        have hs : 0 < Real.sqrt 2 := sqrt_two_pos
        nlinarith
      change (∑ i, aliceZero.play 0 (fun m => s (duel aliceZero s m)) (2 * m) i) + 0 ≤ _
      norm_num only [add_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hsum hthr ⊢
      linarith
    · intro hodd
      exact False.elim ((Nat.not_even_iff_odd.mpr hodd) heven)) hw

theorem imo2025_p5 :
    ({c : ℝ | ∃ s : Strategy, s.Winning c 0}, {c : ℝ | ∃ s : Strategy, s.Winning c 1}) =
      answer := by
  ext c <;> simp only [Set.mem_setOf_eq, Set.mem_Ioi, Set.mem_Iio]
  · exact ⟨fun h => lt_of_not_ge (fun hc => alice_not_winning_of_le hc h), alice_wins_of_lt⟩
  · exact ⟨fun h => lt_of_not_ge (fun hc => bazza_not_winning_of_le hc h), bazza_wins_of_lt⟩

end Imo2025P5
