module

public import Mathlib.Tactic
public import Mathlib.Data.ENat.Basic
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Bounds.Basic

public section Imo2025P3Section
namespace IMO2025P3

open Int

def Bonza (f : ℕ+ → ℕ+) : Prop :=
  ∀ a b : ℕ+, (f a : Int) ∣ ((b : Int) ^ (a : ℕ) - (f b : Int) ^ (f a : ℕ))

def is_valid_c (c : ℝ) : Prop :=
  ∀ (f : ℕ+ → ℕ+), Bonza f → ∀ n, (f n : ℝ) ≤ c * (n : ℝ)

private lemma self_dvd (f : ℕ+ → ℕ+) (hf : Bonza f) (n : ℕ+) :
    (f n : ℕ) ∣ (n : ℕ) ^ (n : ℕ) := by
  rw [← Int.natCast_dvd_natCast]
  have h := hf n n
  have hpow : (f n : ℤ) ∣ (f n : ℤ) ^ (f n : ℕ) :=
    dvd_pow_self _ (by exact_mod_cast (f n).property.ne')
  simpa using h.add hpow

private lemma prime_dvd_input (f : ℕ+ → ℕ+) (hf : Bonza f) {p : ℕ}
    (hp : p.Prime) (n : ℕ+) (hdiv : p ∣ (f n : ℕ)) : p ∣ (n : ℕ) := by
  exact hp.dvd_of_dvd_pow (hdiv.trans (self_dvd f hf n))

private lemma prime_activates (f : ℕ+ → ℕ+) (hf : Bonza f) {p : ℕ}
    (hp : p.Prime) (n : ℕ+) (hdiv : p ∣ (f n : ℕ)) :
    p ∣ (f ⟨p, hp.pos⟩ : ℕ) := by
  let pp : ℕ+ := ⟨p, hp.pos⟩
  have hcast : (p : ℤ) ∣ (f n : ℤ) := Int.natCast_dvd_natCast.mpr hdiv
  have hdiff : (p : ℤ) ∣ (p : ℤ) ^ (n : ℕ) - (f pp : ℤ) ^ (f n : ℕ) :=
    hcast.trans (hf n pp)
  have hpPow : (p : ℤ) ∣ (p : ℤ) ^ (n : ℕ) :=
    dvd_pow_self _ (by exact_mod_cast n.property.ne')
  have hfpPow : (p : ℤ) ∣ (f pp : ℤ) ^ (f n : ℕ) := by
    simpa using hpPow.sub hdiff
  have hfpPowNat : p ∣ (f pp : ℕ) ^ (f n : ℕ) := by
    rw [← Int.natCast_dvd_natCast]
    exact_mod_cast hfpPow
  exact hp.dvd_of_dvd_pow hfpPowNat

private lemma frobenius_prime_pow_modEq {p : ℕ} (hp : p.Prime) (x : ℤ) :
    ∀ k : ℕ, x ^ (p ^ k) ≡ x [ZMOD p]
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ, pow_mul]
      exact (Int.ModEq.pow_prime_eq_self hp (x ^ (p ^ k))).trans
        (frobenius_prime_pow_modEq hp x k)

private lemma active_modEq (f : ℕ+ → ℕ+) (hf : Bonza f) {p : ℕ}
    (hp : p.Prime) (hactive : p ∣ (f ⟨p, hp.pos⟩ : ℕ)) (n : ℕ+) :
    (n : ℕ) ≡ (f n : ℕ) [MOD p] := by
  let pp : ℕ+ := ⟨p, hp.pos⟩
  obtain ⟨k, _hk, hfp⟩ := (Nat.dvd_prime_pow hp).mp (self_dvd f hf pp)
  have hp_fpp : (p : ℤ) ∣ (f pp : ℤ) := Int.natCast_dvd_natCast.mpr hactive
  have hdiff : (p : ℤ) ∣ (n : ℤ) ^ p - (f n : ℤ) ^ (f pp : ℕ) :=
    hp_fpp.trans (hf pp n)
  have hmiddle : (f n : ℤ) ^ (f pp : ℕ) ≡ (n : ℤ) ^ p [ZMOD p] :=
    Int.modEq_iff_dvd.mpr hdiff
  have hI : (n : ℤ) ≡ (f n : ℤ) [ZMOD p] :=
    (Int.ModEq.pow_prime_eq_self hp (n : ℤ)).symm |>.trans
      (hmiddle.symm.trans (by simpa [hfp] using frobenius_prime_pow_modEq hp (f n : ℤ) k))
  exact Int.natCast_modEq_iff.mp hI

private lemma odd_active_identity (f : ℕ+ → ℕ+) (hf : Bonza f) {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hactive : p ∣ (f ⟨p, hp.pos⟩ : ℕ)) :
    ∀ n : ℕ+, f n = n := by
  intro n
  have hpgt : 2 < p := by
    rcases hpodd with ⟨r, hr⟩
    have := hp.two_le
    omega
  obtain ⟨q, hqbig, hqprime, hqmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq
      (max (n : ℕ) (f n : ℕ)) hp.ne_zero (Nat.coprime_two_left.mpr hpodd)
  let qq : ℕ+ := ⟨q, hqprime.pos⟩
  have hqn : (n : ℕ) < q := lt_of_le_of_lt (Nat.le_max_left _ _) hqbig
  have hqfn : (f n : ℕ) < q := lt_of_le_of_lt (Nat.le_max_right _ _) hqbig
  have hqactive : q ∣ (f qq : ℕ) := by
    obtain ⟨k, _hk, hfq⟩ := (Nat.dvd_prime_pow hqprime).mp (self_dvd f hf qq)
    by_contra hnot
    have hkzero : k = 0 := by
      by_contra hk
      exact hnot (hfq ▸ dvd_pow_self q hk)
    have hfqone : (f qq : ℕ) = 1 := by simp [hfq, hkzero]
    have htwoone : 2 ≡ 1 [MOD p] :=
      hqmod.symm.trans (by simpa [hfqone] using active_modEq f hf hp hactive qq)
    have : (2 : ℕ) = 1 := htwoone.eq_of_lt_of_lt hpgt (by omega)
    omega
  exact PNat.eq ((active_modEq f hf hqprime hqactive n).eq_of_lt_of_lt hqn hqfn).symm

private lemma value_power_two (f : ℕ+ → ℕ+) (hf : Bonza f)
    (hnot : ¬∀ n : ℕ+, f n = n) (n : ℕ+) :
    ∃ k : ℕ, (f n : ℕ) = 2 ^ k := by
  refine ⟨(f n : ℕ).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd (f n).property.ne' ?_⟩
  intro d hd hdf
  rcases hd.eq_two_or_odd with htwo | hodd
  · exact htwo
  · exact (hnot (odd_active_identity f hf hd (Nat.odd_iff.mpr hodd)
      (prime_activates f hf hd n hdf))).elim

private lemma odd_input_value_one (f : ℕ+ → ℕ+) (hf : Bonza f)
    (hnot : ¬∀ n : ℕ+, f n = n) (n : ℕ+) (hnodd : Odd (n : ℕ)) :
    (f n : ℕ) = 1 := by
  obtain ⟨k, hfn⟩ := value_power_two f hf hnot n
  by_cases hk : k = 0
  · simp [hfn, hk]
  · have htwo_fn : 2 ∣ (f n : ℕ) := hfn.symm ▸ dvd_pow_self 2 hk
    have htwo_n := prime_dvd_input f hf Nat.prime_two n htwo_fn
    exfalso
    apply Nat.not_even_iff_odd.mpr hnodd
    rcases htwo_n with ⟨r, hr⟩
    exact ⟨r, by omega⟩

private lemma even_input_bound (f : ℕ+ → ℕ+) (hf : Bonza f)
    (hnot : ¬∀ n : ℕ+, f n = n) (n : ℕ+) (hneven : Even (n : ℕ)) :
    (f n : ℕ) ≤ 4 * (n : ℕ) := by
  obtain ⟨k, hfn⟩ := value_power_two f hf hnot n
  let three : ℕ+ := ⟨3, by omega⟩
  have hfthree : (f three : ℕ) = 1 :=
    odd_input_value_one f hf hnot three (by norm_num [three])
  have hfthreePNat : f three = 1 := PNat.eq hfthree
  have hdivInt := hf n three
  rw [hfthreePNat] at hdivInt
  have hfnInt : (f n : ℤ) = (2 ^ k : ℕ) := by exact_mod_cast hfn
  rw [hfnInt] at hdivInt
  have hdiv : 2 ^ k ∣ 3 ^ (n : ℕ) - 1 := by
    rw [← Int.natCast_dvd_natCast, Int.ofNat_sub]
    · simpa [three] using hdivInt
    · exact Nat.one_le_pow _ _ (by omega)
  have hn0 : (n : ℕ) ≠ 0 := n.property.ne'
  have hsub0 : 3 ^ (n : ℕ) - 1 ≠ 0 := by
    have := Nat.one_lt_pow hn0 (by omega : 1 < 3)
    omega
  have hkval : k ≤ padicValNat 2 (3 ^ (n : ℕ) - 1) :=
    (padicValNat_dvd_iff_le hsub0).mp hdiv
  have hval : padicValNat 2 (3 ^ (n : ℕ) - 1) = padicValNat 2 (n : ℕ) + 2 := by
    have h := padicValNat.pow_two_sub_one (x := 3) (n := (n : ℕ))
      (by omega) (by norm_num) hn0 hneven
    have hv4 : padicValNat 2 4 = 2 := by
      exact padicValNat_base_pow (p := 2) (by omega) 2
    have hv2 : padicValNat 2 2 = 1 := by
      exact padicValNat_base_pow (p := 2) (by omega) 1
    norm_num only at h
    rw [hv4, hv2] at h
    omega
  have hk : k ≤ padicValNat 2 (n : ℕ) + 2 := hval ▸ hkval
  calc
    (f n : ℕ) = 2 ^ k := hfn
    _ ≤ 2 ^ (padicValNat 2 (n : ℕ) + 2) := Nat.pow_le_pow_right (by omega) hk
    _ = 4 * 2 ^ padicValNat 2 (n : ℕ) := by rw [pow_add]; ring
    _ ≤ 4 * (n : ℕ) := Nat.mul_le_mul_left 4
      (Nat.le_of_dvd n.property pow_padicValNat_dvd)

theorem four_valid : is_valid_c 4 := by
  intro f hf n
  by_cases hid : ∀ m : ℕ+, f m = m
  · rw [hid n]
    norm_num
  · rcases Nat.even_or_odd (n : ℕ) with hneven | hnodd
    · exact_mod_cast even_input_bound f hf hid n hneven
    · have hfn : (f n : ℕ) = 1 := odd_input_value_one f hf hid n hnodd
      have hn : (1 : ℝ) ≤ 4 * (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.property
        nlinarith
      simpa [hfn] using hn

private def extremalValue (n : ℕ) : ℕ :=
  if Odd n then 1 else if n = 4 then 16 else 2

private lemma extremalValue_pos (n : ℕ) : 0 < extremalValue n := by
  unfold extremalValue
  split
  · norm_num
  · split <;> norm_num

private def extremal (n : ℕ+) : ℕ+ :=
  ⟨extremalValue n, extremalValue_pos n⟩

private lemma odd_natCast_int {n : ℕ} (hn : Odd n) : Odd (n : ℤ) := by
  rcases hn with ⟨k, hk⟩
  refine ⟨(k : ℤ), ?_⟩
  exact_mod_cast hk

private lemma two_dvd_intCast_of_even {n : ℕ} (hn : Even n) :
    (2 : ℤ) ∣ (n : ℤ) := by
  rcases hn with ⟨k, hk⟩
  refine ⟨(k : ℤ), ?_⟩
  norm_cast
  omega

private lemma sixteen_dvd_odd_fourth_sub_one {z : ℤ} (hz : Odd z) :
    (16 : ℤ) ∣ z ^ 4 - 1 := by
  rcases hz with ⟨k, rfl⟩
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
  refine ⟨m * (2 * k ^ 2 + 2 * k + 1), ?_⟩
  calc
    (2 * k + 1) ^ 4 - 1 =
        8 * (k * (k + 1)) * (2 * k ^ 2 + 2 * k + 1) := by ring
    _ = 16 * (m * (2 * k ^ 2 + 2 * k + 1)) := by rw [hm]; ring

private theorem extremal_bonza : Bonza extremal := by
  intro a b
  by_cases ha : Odd (a : ℕ)
  · simp [extremal, extremalValue, ha]
  by_cases ha4 : (a : ℕ) = 4
  · by_cases hb : Odd (b : ℕ)
    · simpa [extremal, extremalValue, ha, ha4, hb] using
        sixteen_dvd_odd_fourth_sub_one (odd_natCast_int hb)
    · have hbEven : Even (b : ℕ) := Nat.not_odd_iff_even.mp hb
      have hbTwo : (2 : ℤ) ∣ (b : ℤ) := two_dvd_intCast_of_even hbEven
      have hbSixteen : (16 : ℤ) ∣ (b : ℤ) ^ 4 := by
        simpa using pow_dvd_pow_of_dvd hbTwo 4
      have hfbSixteen : (16 : ℤ) ∣ (extremal b : ℤ) ^ 16 := by
        simp [extremal, extremalValue, hb]
        split <;> norm_num
      simpa [extremal, extremalValue, ha, ha4] using
        dvd_sub hbSixteen hfbSixteen
  · by_cases hb : Odd (b : ℕ)
    · have hbPowOdd : Odd ((b : ℤ) ^ (a : ℕ)) := (odd_natCast_int hb).pow
      rcases hbPowOdd with ⟨k, hk⟩
      have htwo : (2 : ℤ) ∣ (b : ℤ) ^ (a : ℕ) - 1 := by
        refine ⟨k, ?_⟩
        omega
      simpa [extremal, extremalValue, ha, ha4, hb] using htwo
    · have hbEven : Even (b : ℕ) := Nat.not_odd_iff_even.mp hb
      have hbTwo : (2 : ℤ) ∣ (b : ℤ) := two_dvd_intCast_of_even hbEven
      have hbPowTwo : (2 : ℤ) ∣ (b : ℤ) ^ (a : ℕ) :=
        dvd_pow hbTwo (Nat.ne_of_gt a.property)
      have hfbPowTwo : (2 : ℤ) ∣ (extremal b : ℤ) ^ 2 := by
        simp [extremal, extremalValue, hb]
        split <;> norm_num
      simpa [extremal, extremalValue, ha, ha4] using
        dvd_sub hbPowTwo hfbPowTwo

private theorem four_lower {c : ℝ} (hc : is_valid_c c) : 4 ≤ c := by
  have h := hc extremal extremal_bonza (⟨4, by norm_num⟩ : ℕ+)
  norm_num [extremal, extremalValue] at h
  nlinarith

/- determine -/ abbrev answer : ℝ := 4

theorem imo2025_p3 :
    IsLeast {c : ℝ | is_valid_c c} answer := by
  refine ⟨four_valid, ?_⟩
  intro c hc
  exact four_lower hc

end IMO2025P3
end Imo2025P3Section
