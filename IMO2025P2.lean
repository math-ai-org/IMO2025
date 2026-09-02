module
public import Mathlib
public section

open scoped Real
open Affine EuclideanGeometry Module

namespace IMO2025P2

private lemma inner_coordinates
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {c d x y : V} (q g z₁ w₁ z₂ w₂ : ℝ)
    (hc : @inner ℝ V _ c c = q) (hd : @inner ℝ V _ d d = q)
    (hcd : @inner ℝ V _ c d = g)
    (hx : x = z₁ • c + w₁ • d) (hy : y = z₂ • c + w₂ • d) :
    @inner ℝ V _ x y = q * (z₁ * z₂ + w₁ * w₂) + g * (z₁ * w₂ + w₁ * z₂) := by
  subst x
  subst y
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [hc, hd, hcd]
  have hdc : @inner ℝ V _ d c = g := by
    calc
      @inner ℝ V _ d c = @inner ℝ V _ c d := (real_inner_comm d c).symm
      _ = g := hcd
  rw [hdc]
  simp
  ring

private lemma affine_coordinates_of_independent
    {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace Pt] [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]
    {P C D X : Pt} (h : AffineIndependent ℝ ![P, C, D]) :
    ∃ x y : ℝ, X -ᵥ P = x • (C -ᵥ P) + y • (D -ᵥ P) := by
  have hli : LinearIndependent ℝ ![C -ᵥ P, D -ᵥ P] := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ ![P, C, D] 0,
      ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))] at h
    convert h using 1
    ext i
    fin_cases i <;> rfl
  let bas : Basis (Fin 2) ℝ V := basisOfLinearIndependentOfCardEqFinrank hli (by
    simpa using (Fact.out : finrank ℝ V = 2).symm)
  let c := bas.repr (X -ᵥ P)
  have hx : X -ᵥ P = c 0 • (C -ᵥ P) + c 1 • (D -ᵥ P) := by
    rw [← bas.sum_repr (X -ᵥ P), Fin.sum_univ_two]
    dsimp only [c]
    rw [show bas 0 = (C -ᵥ P) by
      change basisOfLinearIndependentOfCardEqFinrank hli _ 0 = _
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      rfl]
    rw [show bas 1 = (D -ᵥ P) by
      change basisOfLinearIndependentOfCardEqFinrank hli _ 1 = _
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      rfl]
  exact ⟨c 0, c 1, hx⟩

private lemma ordered_four_coordinates
    {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace Pt] [NormedAddTorsor V Pt]
    {C M N D : Pt} (h : [C, M, N, D].Sbtw ℝ) :
    ∃ u v : ℝ, 0 < u ∧ u < v ∧ v < 1 ∧
      M = AffineMap.lineMap C D u ∧ N = AffineMap.lineMap C D v := by
  have hCMD : Sbtw ℝ C M D := (List.sbtw_four.mp h).2.1
  have hCND : Sbtw ℝ C N D := (List.sbtw_four.mp h).2.2.1
  rcases hCMD.mem_image_Ioo with ⟨u, hu, huM⟩
  rcases hCND.mem_image_Ioo with ⟨v, hv, hvN⟩
  use u, v
  refine ⟨hu.1, ?_, hv.2, huM.symm, hvN.symm⟩
  by_contra huv
  rw [not_lt] at huv
  have hNCM : Wbtw ℝ C N M := by
    rw [← huM, ← hvN]
    simpa [AffineMap.lineMap_apply] using
      wbtw_smul_vadd_smul_vadd_of_nonneg_of_le C (D -ᵥ C) hv.1.le huv
  have hNM : N = M := hNCM.swap_right_iff.mp (List.sbtw_four.mp h).1.wbtw
  exact (List.sbtw_four.mp h).2.2.2.left_ne hNM.symm

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace Pt] [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

set_option maxHeartbeats 50000000 in
theorem imo2025_p2
    {M N A B C D P E F H : Pt} {Ω Γ : Sphere Pt}
    (Ω_center_eq_M : Ω.center = M)
    (Γ_center_eq_N : Γ.center = N)
    (Ω_radius_lt_Γ_radius : Ω.radius < Γ.radius)
    (A_mem_inter : A ∈ (Ω ∩ Γ : Set Pt))
    (B_mem_inter : B ∈ (Ω ∩ Γ : Set Pt))
    (A_ne_B : A ≠ B)
    (M_ne_N : M ≠ N)
    (C_mem_inter : C ∈ (line[ℝ, M, N] ∩ Ω : Set Pt))
    (D_mem_inter : D ∈ (line[ℝ, M, N] ∩ Γ : Set Pt))
    (sbtw_C_M_N_D : [C, M, N, D].Sbtw ℝ)
    (affineIndependent_ACD : AffineIndependent ℝ ![A, C, D])
    (P_eq_circumcenter : P =
      (⟨_, affineIndependent_ACD⟩ : Triangle ℝ Pt).circumcenter)
    (E_mem_inter : E ∈ (line[ℝ, A, P] ∩ Ω : Set Pt))
    (E_ne_A : E ≠ A)
    (F_mem_inter : F ∈ (line[ℝ, A, P] ∩ Γ : Set Pt))
    (F_ne_A : F ≠ A)
    (affineIndependent_PMN : AffineIndependent ℝ ![P, M, N])
    (H_eq_orthocenter : H =
      Triangle.orthocenter
        (⟨_, affineIndependent_PMN⟩ : Triangle ℝ Pt)) :
    ∃ affineIndependent_BEF : AffineIndependent ℝ ![B, E, F],
      (⟨_, affineIndependent_BEF⟩ : Triangle ℝ Pt).circumsphere.IsTangent
        (AffineSubspace.mk' H line[ℝ, A, P].direction) := by
  haveI : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  rcases A_mem_inter with ⟨AΩ, AΓ⟩
  rcases B_mem_inter with ⟨BΩ, BΓ⟩
  rcases C_mem_inter with ⟨Cline, CΩ⟩
  rcases D_mem_inter with ⟨Dline, DΓ⟩
  rcases E_mem_inter with ⟨Eline, EΩ⟩
  rcases F_mem_inter with ⟨Fline, FΓ⟩
  subst M
  subst N
  subst P
  subst H
  let tACD : Triangle ℝ Pt := ⟨![A, C, D], affineIndependent_ACD⟩
  let P₀ : Pt := tACD.circumcenter
  let c : V := C -ᵥ P₀
  let d : V := D -ᵥ P₀
  let a : V := A -ᵥ P₀
  have hAC : dist A P₀ = dist C P₀ := by
    exact (tACD.dist_circumcenter_eq_circumradius 0).trans
      (tACD.dist_circumcenter_eq_circumradius 1).symm
  have hAD : dist A P₀ = dist D P₀ := by
    exact (tACD.dist_circumcenter_eq_circumradius 0).trans
      (tACD.dist_circumcenter_eq_circumradius 2).symm
  have hqC : @inner ℝ V _ c c = dist A P₀ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub, ← hAC]
  have hqD : @inner ℝ V _ d d = dist A P₀ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub, ← hAD]
  obtain ⟨u, v, hu, huv, hv, hM, hN⟩ := ordered_four_coordinates sbtw_C_M_N_D
  have hMv : Ω.center -ᵥ P₀ = (1 - u) • c + u • d := by
    rw [hM, AffineMap.lineMap_apply, vadd_vsub_assoc]
    dsimp only [c, d]
    rw [show D -ᵥ C = (D -ᵥ P₀) - (C -ᵥ P₀) by
      exact (vsub_sub_vsub_cancel_right D C P₀).symm]
    module
  have hNv : Γ.center -ᵥ P₀ = (1 - v) • c + v • d := by
    rw [hN, AffineMap.lineMap_apply, vadd_vsub_assoc]
    dsimp only [c, d]
    rw [show D -ᵥ C = (D -ᵥ P₀) - (C -ᵥ P₀) by
      exact (vsub_sub_vsub_cancel_right D C P₀).symm]
    module
  have hu0 : u ≠ 0 := hu.ne'
  have hv1 : 1 - v ≠ 0 := sub_ne_zero.mpr hv.ne'
  have hai_PCD : AffineIndependent ℝ ![P₀, C, D] := by
    have hCMN : Collinear ℝ {Ω.center, Γ.center, C} := by
      convert (List.sbtw_four.mp sbtw_C_M_N_D).1.wbtw.collinear using 1 <;> aesop
    have hPMc : AffineIndependent ℝ ![P₀, Ω.center, C] :=
      affineIndependent_of_affineIndependent_collinear_ne affineIndependent_PMN hCMN
        (List.sbtw_four.mp sbtw_C_M_N_D).1.left_ne.symm
    have hCMD : Collinear ℝ {C, Ω.center, D} :=
      (List.sbtw_four.mp sbtw_C_M_N_D).2.1.wbtw.collinear
    exact affineIndependent_of_affineIndependent_collinear_ne hPMc.comm_right hCMD
      (List.sbtw_four.mp sbtw_C_M_N_D).2.1.left_ne_right
  obtain ⟨x, y, hAv⟩ := affine_coordinates_of_independent
    (P := P₀) (C := C) (D := D) (X := A) hai_PCD
  change a = x • c + y • d at hAv
  have hACinner : @inner ℝ V _ a a = @inner ℝ V _ c c := by
    dsimp only [a, c]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub,
      ← dist_eq_norm_vsub, hAC]
  have hADinner : @inner ℝ V _ a a = @inner ℝ V _ d d := by
    dsimp only [a, d]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub,
      ← dist_eq_norm_vsub, hAD]
  have hq : 0 < @inner ℝ V _ c c := by
    rw [real_inner_self_pos]
    exact vsub_ne_zero.mpr (hai_PCD.injective.ne (by decide : (1 : Fin 3) ≠ 0))
  have hxyC :
      @inner ℝ V _ a c = x * @inner ℝ V _ c c + y * @inner ℝ V _ d c := by
    rw [hAv]
    simp [inner_add_left, inner_smul_left]
  have hxyD :
      @inner ℝ V _ a d = x * @inner ℝ V _ c d + y * @inner ℝ V _ d d := by
    rw [hAv]
    simp [inner_add_left, inner_smul_left]
  have hAΩdist : dist A Ω.center = dist C Ω.center :=
    dist_center_eq_dist_center_of_mem_sphere AΩ CΩ
  have hAΓdist : dist A Γ.center = dist D Γ.center :=
    dist_center_eq_dist_center_of_mem_sphere AΓ DΓ
  have hAΩinner : @inner ℝ V _ (Ω.center -ᵥ P₀) (c - a) = 0 := by
    have hz := inner_vsub_vsub_of_dist_eq_of_dist_eq
      (c₁ := P₀) (c₂ := Ω.center) (p₁ := A) (p₂ := C) hAC hAΩdist
    simpa only [show C -ᵥ A = c - a by
      dsimp only [c, a]
      exact (vsub_sub_vsub_cancel_right C A P₀).symm] using hz
  have hAΓinner : @inner ℝ V _ (Γ.center -ᵥ P₀) (d - a) = 0 := by
    have hz := inner_vsub_vsub_of_dist_eq_of_dist_eq
      (c₁ := P₀) (c₂ := Γ.center) (p₁ := A) (p₂ := D) hAD hAΓdist
    simpa only [show D -ᵥ A = d - a by
      dsimp only [d, a]
      exact (vsub_sub_vsub_cancel_right D A P₀).symm] using hz
  have hMscalar :
      (1 - x) * ((1 - u) * ‖c‖ ^ 2 + u * @inner ℝ V _ d c) -
        y * ((1 - u) * @inner ℝ V _ c d + u * ‖d‖ ^ 2) = 0 := by
    rw [hMv, hAv] at hAΩinner
    simp only [inner_add_left, inner_add_right, inner_sub_right, inner_smul_left,
      inner_smul_right, real_inner_self_eq_norm_sq] at hAΩinner
    simp at hAΩinner
    ring_nf at hAΩinner ⊢
    exact hAΩinner
  have hNscalar :
      -x * ((1 - v) * ‖c‖ ^ 2 + v * @inner ℝ V _ d c) +
        (1 - y) * ((1 - v) * @inner ℝ V _ c d + v * ‖d‖ ^ 2) = 0 := by
    rw [hNv, hAv] at hAΓinner
    simp only [inner_add_left, inner_add_right, inner_sub_right, inner_smul_left,
      inner_smul_right, real_inner_self_eq_norm_sq] at hAΓinner
    simp at hAΓinner
    ring_nf at hAΓinner ⊢
    exact hAΓinner
  have hAvnorm :
      ‖a‖ ^ 2 = x ^ 2 * ‖c‖ ^ 2 + y ^ 2 * ‖d‖ ^ 2 +
        2 * x * y * @inner ℝ V _ c d := by
    rw [hAv, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, inner_smul_left, inner_smul_right]
    change (|x| * ‖c‖) ^ 2 + 2 * (x * (y * @inner ℝ V _ c d)) +
      (|y| * ‖d‖) ^ 2 = _
    simp only [mul_pow, sq_abs]
    ring
  have hcdcomm : @inner ℝ V _ d c = @inner ℝ V _ c d := (real_inner_comm d c).symm
  have hnormcd : ‖c‖ ^ 2 = ‖d‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hqC, hqD]
  have hnorma : ‖a‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hACinner]
  rw [hcdcomm, ← hnormcd] at hMscalar hNscalar
  rw [hnorma, hnormcd] at hAvnorm
  have hli_cd : LinearIndependent ℝ ![c, d] := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ ![P₀, C, D] 0,
      ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))] at hai_PCD
    convert hai_PCD using 1
    ext i
    fin_cases i <;> rfl
  have hgram0 : ‖c‖ ^ 4 - (@inner ℝ V _ c d) ^ 2 ≠ 0 := by
    have hp := (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)
      (v := ![c, d])).2 hli_cd
    simp [Matrix.gram, Matrix.det_fin_two, real_inner_comm d c] at hp
    rw [← hnormcd] at hp
    rw [show @inner ℝ V _ d c = @inner ℝ V _ c d by
      exact (real_inner_comm d c).symm] at hp
    convert hp using 1 <;> ring
  let aa : ℝ := (1 - u) * ‖c‖ ^ 2 + u * @inner ℝ V _ c d
  let bb : ℝ := (1 - u) * @inner ℝ V _ c d + u * ‖c‖ ^ 2
  let cc : ℝ := (1 - v) * ‖c‖ ^ 2 + v * @inner ℝ V _ c d
  let dd : ℝ := (1 - v) * @inner ℝ V _ c d + v * ‖c‖ ^ 2
  have hMlin : aa * x + bb * y = aa := by
    dsimp only [aa, bb]
    linear_combination -hMscalar
  have hNlin : cc * x + dd * y = dd := by
    dsimp only [cc, dd]
    linear_combination -hNscalar
  have hdet : aa * dd - bb * cc =
      (v - u) * (‖c‖ ^ 4 - (@inner ℝ V _ c d) ^ 2) := by
    dsimp only [aa, bb, cc, dd]
    ring
  have hdet0 : aa * dd - bb * cc ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (sub_ne_zero.mpr huv.ne') hgram0
  have hxdet : (aa * dd - bb * cc) * x = dd * (aa - bb) := by
    linear_combination dd * hMlin - bb * hNlin
  have hydet : (aa * dd - bb * cc) * y = aa * (dd - cc) := by
    linear_combination aa * hNlin - cc * hMlin
  have hx : x = dd * (aa - bb) / (aa * dd - bb * cc) := by
    rw [eq_div_iff hdet0]
    calc
      x * (aa * dd - bb * cc) = (aa * dd - bb * cc) * x := mul_comm _ _
      _ = dd * (aa - bb) := hxdet
  have hy : y = aa * (dd - cc) / (aa * dd - bb * cc) := by
    rw [eq_div_iff hdet0]
    calc
      y * (aa * dd - bb * cc) = (aa * dd - bb * cc) * y := mul_comm _ _
      _ = aa * (dd - cc) := hydet
  rw [hx, hy] at hAvnorm
  have hAvnorm_clear :
      (aa * dd - bb * cc) ^ 2 * ‖c‖ ^ 2 =
        (dd * (aa - bb)) ^ 2 * ‖c‖ ^ 2 +
        (aa * (dd - cc)) ^ 2 * ‖c‖ ^ 2 +
        2 * (dd * (aa - bb)) * (aa * (dd - cc)) * @inner ℝ V _ c d := by
    field_simp [hdet0] at hAvnorm
    rw [← hnormcd] at hAvnorm
    have hdcomm : dd * aa - bb * cc = aa * dd - bb * cc := by ring
    rw [hdcomm] at hAvnorm
    have hz := (eq_div_iff (pow_ne_zero 2 hdet0)).mp hAvnorm
    ring_nf at hz ⊢
    exact hz
  have hcircle_relation :
      (1 - 2 * u) * (1 - 2 * v) *
          (‖c‖ ^ 2 - @inner ℝ V _ c d) ^ 2 *
          (‖c‖ ^ 2 * (1 - 2 * v + 2 * u * v) +
            2 * @inner ℝ V _ c d * u * (1 - v)) = 0 := by
    have hfac :
        (aa * dd - bb * cc) ^ 2 * ‖c‖ ^ 2 -
          ((dd * (aa - bb)) ^ 2 * ‖c‖ ^ 2 +
            (aa * (dd - cc)) ^ 2 * ‖c‖ ^ 2 +
            2 * (dd * (aa - bb)) * (aa * (dd - cc)) * @inner ℝ V _ c d) =
        -((‖c‖ ^ 4 - (@inner ℝ V _ c d) ^ 2) *
          (1 - 2 * u) * (1 - 2 * v) *
          (‖c‖ ^ 2 - @inner ℝ V _ c d) ^ 2 *
          (‖c‖ ^ 2 * (1 - 2 * v + 2 * u * v) +
            2 * @inner ℝ V _ c d * u * (1 - v))) := by
      dsimp only [aa, bb, cc, dd]
      ring
    have hprodneg :
        -((‖c‖ ^ 4 - (@inner ℝ V _ c d) ^ 2) *
          ((1 - 2 * u) * (1 - 2 * v) *
          (‖c‖ ^ 2 - @inner ℝ V _ c d) ^ 2 *
          (‖c‖ ^ 2 * (1 - 2 * v + 2 * u * v) +
            2 * @inner ℝ V _ c d * u * (1 - v)))) = 0 := by
      calc
        _ = -((‖c‖ ^ 4 - (@inner ℝ V _ c d) ^ 2) *
          (1 - 2 * u) * (1 - 2 * v) *
          (‖c‖ ^ 2 - @inner ℝ V _ c d) ^ 2 *
          (‖c‖ ^ 2 * (1 - 2 * v + 2 * u * v) +
            2 * @inner ℝ V _ c d * u * (1 - v))) := by ring
        _ = (aa * dd - bb * cc) ^ 2 * ‖c‖ ^ 2 -
          ((dd * (aa - bb)) ^ 2 * ‖c‖ ^ 2 +
            (aa * (dd - cc)) ^ 2 * ‖c‖ ^ 2 +
            2 * (dd * (aa - bb)) * (aa * (dd - cc)) * @inner ℝ V _ c d) := hfac.symm
        _ = 0 := sub_eq_zero.mpr hAvnorm_clear
    have hprod := neg_eq_zero.mp hprodneg
    exact (mul_eq_zero.mp hprod).resolve_left hgram0
  have h1mu : 0 < 1 - u := sub_pos.mpr (huv.trans hv)
  have h1mv : 0 < 1 - v := sub_pos.mpr hv
  have hradΩ : Ω.radius = u * dist C D := by
    rw [← mem_sphere.1 CΩ, hM, dist_left_lineMap, Real.norm_eq_abs,
      abs_of_pos hu]
  have hradΓ : Γ.radius = (1 - v) * dist C D := by
    rw [← mem_sphere.1 DΓ, hN, dist_comm, dist_lineMap_right,
      Real.norm_eq_abs, abs_of_pos h1mv]
  have hdistCD : 0 < dist C D := dist_pos.mpr
    (List.sbtw_four.mp sbtw_C_M_N_D).2.1.left_ne_right
  have huvsum : u < 1 - v := by
    rw [hradΩ, hradΓ] at Ω_radius_lt_Γ_radius
    exact lt_of_mul_lt_mul_right Ω_radius_lt_Γ_radius (le_of_lt hdistCD)
  have h2u0 : 1 - 2 * u ≠ 0 := by
    intro huzero
    have huhalf : u = 1 / 2 := by linarith
    have hMmid : Ω.center = midpoint ℝ C D := by
      rw [hM, huhalf, lineMap_one_half]
    have hdiam : Ω.IsDiameter C D :=
      Sphere.isDiameter_iff_left_mem_and_midpoint_eq_center.2 ⟨CΩ, hMmid.symm⟩
    have DΩ : D ∈ Ω := hdiam.right_mem
    have hspheres : Ω ≠ tACD.circumsphere := by
      intro heq
      have hcent : Ω.center = P₀ := by
        change Ω.center = tACD.circumsphere.center
        rw [heq]
      exact (affineIndependent_PMN.injective.ne (by decide : (1 : Fin 3) ≠ 0)) hcent
    have hA := eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (Fact.out : finrank ℝ V = 2) hspheres
      (hai_PCD.injective.ne (by decide : (1 : Fin 3) ≠ 2))
      CΩ DΩ AΩ (tACD.mem_circumsphere 1) (tACD.mem_circumsphere 2)
      (tACD.mem_circumsphere 0)
    rcases hA with hAC' | hAD'
    · exact (affineIndependent_ACD.injective.ne (by decide : (0 : Fin 3) ≠ 1)) hAC'
    · exact (affineIndependent_ACD.injective.ne (by decide : (0 : Fin 3) ≠ 2)) hAD'
  have h2v0 : 1 - 2 * v ≠ 0 := by
    intro hvzero
    have hvhalf : v = 1 / 2 := by linarith
    have hNmid : Γ.center = midpoint ℝ C D := by
      rw [hN, hvhalf, lineMap_one_half]
    have hdiam : Γ.IsDiameter C D :=
      Sphere.isDiameter_iff_right_mem_and_midpoint_eq_center.2 ⟨DΓ, hNmid.symm⟩
    have CΓ : C ∈ Γ := hdiam.left_mem
    have hspheres : Γ ≠ tACD.circumsphere := by
      intro heq
      have hcent : Γ.center = P₀ := by
        change Γ.center = tACD.circumsphere.center
        rw [heq]
      exact (affineIndependent_PMN.injective.ne (by decide : (2 : Fin 3) ≠ 0)) hcent
    have hA := eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (Fact.out : finrank ℝ V = 2) hspheres
      (hai_PCD.injective.ne (by decide : (1 : Fin 3) ≠ 2))
      CΓ DΓ AΓ (tACD.mem_circumsphere 1) (tACD.mem_circumsphere 2)
      (tACD.mem_circumsphere 0)
    rcases hA with hAC' | hAD'
    · exact (affineIndependent_ACD.injective.ne (by decide : (0 : Fin 3) ≠ 1)) hAC'
    · exact (affineIndependent_ACD.injective.ne (by decide : (0 : Fin 3) ≠ 2)) hAD'

  have hqc0 : ‖c‖ ^ 2 - @inner ℝ V _ c d ≠ 0 := by
    intro hz
    apply hgram0
    have hi := sub_eq_zero.mp hz
    calc
      ‖c‖ ^ 4 - (@inner ℝ V _ c d) ^ 2 =
          (‖c‖ ^ 2) ^ 2 - (@inner ℝ V _ c d) ^ 2 := by ring
      _ = 0 := by rw [hi]; ring
  have hbase_relation :
      ‖c‖ ^ 2 * (1 - 2 * v + 2 * u * v) +
        2 * @inner ℝ V _ c d * u * (1 - v) = 0 := by
    have hp := mul_eq_zero.mp hcircle_relation
    rcases hp with hleft | hbase
    · have hp' := mul_eq_zero.mp hleft
      rcases hp' with hleft | hsq
      · have hp'' := mul_eq_zero.mp hleft
        rcases hp'' with hu' | hv'
        · exact False.elim (h2u0 hu')
        · exact False.elim (h2v0 hv')
      · exact False.elim (pow_ne_zero 2 hqc0 hsq)
    · exact hbase
  have huv0 : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
  have hx_simple : x = (1 - v) / (v - u) := by
    rw [hx, hdet]
    dsimp only [aa, bb, cc, dd]
    have hnum :
        (((1 - v) * @inner ℝ V _ c d + v * ‖c‖ ^ 2) *
          (((1 - u) * ‖c‖ ^ 2 + u * @inner ℝ V _ c d) -
            ((1 - u) * @inner ℝ V _ c d + u * ‖c‖ ^ 2))) * (v - u) -
          (1 - v) * ((v - u) * (‖c‖ ^ 4 - (@inner ℝ V _ c d) ^ 2)) =
        (‖c‖ ^ 2 - @inner ℝ V _ c d) * (u - v) *
          (‖c‖ ^ 2 * (1 - 2 * v + 2 * u * v) +
            2 * @inner ℝ V _ c d * u * (1 - v)) := by ring
    rw [hbase_relation, mul_zero] at hnum
    apply (div_eq_div_iff (mul_ne_zero huv0 hgram0) huv0).2
    linear_combination hnum
  have hy_simple : y = u / (v - u) := by
    rw [hy, hdet]
    dsimp only [aa, bb, cc, dd]
    have hnum :
        (((1 - u) * ‖c‖ ^ 2 + u * @inner ℝ V _ c d) *
          (((1 - v) * @inner ℝ V _ c d + v * ‖c‖ ^ 2) -
            ((1 - v) * ‖c‖ ^ 2 + v * @inner ℝ V _ c d))) * (v - u) -
          u * ((v - u) * (‖c‖ ^ 4 - (@inner ℝ V _ c d) ^ 2)) =
        (‖c‖ ^ 2 - @inner ℝ V _ c d) * (u - v) *
          (‖c‖ ^ 2 * (1 - 2 * v + 2 * u * v) +
            2 * @inner ℝ V _ c d * u * (1 - v)) := by ring
    rw [hbase_relation, mul_zero] at hnum
    apply (div_eq_div_iff (mul_ne_zero huv0 hgram0) huv0).2
    linear_combination hnum
  rw [hx_simple, hy_simple] at hAv
  have hAv_final :
      a = ((1 - v) / (v - u)) • c + (u / (v - u)) • d := hAv
  obtain ⟨e, he⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp Eline
  obtain ⟨f, hf⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp Fline
  have hEv : E -ᵥ P₀ = (1 - e) • a := by
    rw [← he, AffineMap.lineMap_apply, vadd_vsub_assoc]
    change e • (P₀ -ᵥ A) + a = _
    rw [show P₀ -ᵥ A = -a by dsimp only [a]; rw [neg_vsub_eq_vsub_rev]]
    module
  have hFv : F -ᵥ P₀ = (1 - f) • a := by
    rw [← hf, AffineMap.lineMap_apply, vadd_vsub_assoc]
    change f • (P₀ -ᵥ A) + a = _
    rw [show P₀ -ᵥ A = -a by dsimp only [a]; rw [neg_vsub_eq_vsub_rev]]
    module
  have he0 : e ≠ 0 := by
    intro hez
    apply E_ne_A
    rw [← he, hez, AffineMap.lineMap_apply_zero]
  have hf0 : f ≠ 0 := by
    intro hfz
    apply F_ne_A
    rw [← hf, hfz, AffineMap.lineMap_apply_zero]
  have hEeq := dist_center_eq_dist_center_of_mem_sphere EΩ AΩ
  have hFeq := dist_center_eq_dist_center_of_mem_sphere FΓ AΓ
  set_option maxHeartbeats 1000000 in
  have second_parameter
      {X O : Pt} {t : ℝ} (hX : X -ᵥ P₀ = (1 - t) • a)
      (hmemX : dist X O = dist A O) (ht0 : t ≠ 0) :
      t = 2 * @inner ℝ V _ a (A -ᵥ O) / @inner ℝ V _ a a := by
    have ha0 : @inner ℝ V _ a a ≠ 0 := by
      rw [hACinner]
      exact ne_of_gt hq
    have hXO : X -ᵥ O = (1 - t) • a + (P₀ -ᵥ O) := by
      rw [← vsub_add_vsub_cancel X P₀ O, hX]
    have hAO : A -ᵥ O = a + (P₀ -ᵥ O) := by
      rw [← vsub_add_vsub_cancel A P₀ O]
    have hs : ‖(1 - t) • a + (P₀ -ᵥ O)‖ ^ 2 =
        ‖a + (P₀ -ᵥ O)‖ ^ 2 := by
      rw [← hXO, ← hAO, ← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hmemX]
    rw [norm_add_sq_real, norm_add_sq_real, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs] at hs
    have hfac : t *
        (t * @inner ℝ V _ a a - 2 * @inner ℝ V _ a (A -ᵥ O)) = 0 := by
      have hinnerAO : @inner ℝ V _ a (A -ᵥ O) =
          @inner ℝ V _ a a + @inner ℝ V _ a (P₀ -ᵥ O) := by
        rw [hAO, inner_add_right]
      rw [hinnerAO]
      have hsmul : @inner ℝ V _ ((1 - t) • a) (P₀ -ᵥ O) =
          (1 - t) * @inner ℝ V _ a (P₀ -ᵥ O) := by
        rw [inner_smul_left]
        simp
      rw [hsmul, ← real_inner_self_eq_norm_sq] at hs
      ring_nf at hs ⊢
      linear_combination hs
    have hz := (mul_eq_zero.mp hfac).resolve_left ht0
    apply (eq_div_iff ha0).2
    linarith
  have he_formula : e = 2 * @inner ℝ V _ a (A -ᵥ Ω.center) /
      @inner ℝ V _ a a := second_parameter hEv hEeq he0
  have hf_formula : f = 2 * @inner ℝ V _ a (A -ᵥ Γ.center) /
      @inner ℝ V _ a a := second_parameter hFv hFeq hf0
  have haO : @inner ℝ V _ a (A -ᵥ Ω.center) =
      @inner ℝ V _ a a - @inner ℝ V _ a (Ω.center -ᵥ P₀) := by
    rw [show A -ᵥ Ω.center = a - (Ω.center -ᵥ P₀) by
      dsimp only [a]
      exact (vsub_sub_vsub_cancel_right A Ω.center P₀).symm, inner_sub_right]
  have haN : @inner ℝ V _ a (A -ᵥ Γ.center) =
      @inner ℝ V _ a a - @inner ℝ V _ a (Γ.center -ᵥ P₀) := by
    rw [show A -ᵥ Γ.center = a - (Γ.center -ᵥ P₀) by
      dsimp only [a]
      exact (vsub_sub_vsub_cancel_right A Γ.center P₀).symm, inner_sub_right]
  have haMcoord : @inner ℝ V _ a (Ω.center -ᵥ P₀) =
      (1 - u) * @inner ℝ V _ a c + u * @inner ℝ V _ a d := by
    rw [hMv, inner_add_right, inner_smul_right, inner_smul_right]
  have haNcoord : @inner ℝ V _ a (Γ.center -ᵥ P₀) =
      (1 - v) * @inner ℝ V _ a c + v * @inner ℝ V _ a d := by
    rw [hNv, inner_add_right, inner_smul_right, inner_smul_right]
  have haac : @inner ℝ V _ a c =
      ((1 - v) / (v - u)) * @inner ℝ V _ c c +
        (u / (v - u)) * @inner ℝ V _ c d := by
    rw [hAv_final, inner_add_left, inner_smul_left, inner_smul_left]
    have hstar (z : ℝ) : (starRingEnd ℝ) z = z := by simp
    rw [hstar, hstar, hcdcomm]
  have haad : @inner ℝ V _ a d =
      ((1 - v) / (v - u)) * @inner ℝ V _ c d +
        (u / (v - u)) * @inner ℝ V _ d d := by
    rw [hAv_final, inner_add_left, inner_smul_left, inner_smul_left]
    have hstar (z : ℝ) : (starRingEnd ℝ) z = z := by simp
    rw [hstar, hstar]
  have he_scalar : e = 1 + (2 * u - v) / (1 - v) := by
    rw [he_formula, haO, haMcoord, haac, haad]
    have hcc : @inner ℝ V _ c c = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c
    have hdd : @inner ℝ V _ d d = ‖c‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq, ← hnormcd]
    have haa : @inner ℝ V _ a a = ‖c‖ ^ 2 := by
      rw [hACinner, hcc]
    rw [hcc, hdd, haa]
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr
      (vsub_ne_zero.mpr (hai_PCD.injective.ne (by decide : (1 : Fin 3) ≠ 0)))
    field_simp [huv0, hv1, hcpos.ne']
    have hbr := hbase_relation
    ring_nf at hbr ⊢
    linear_combination (u + v - 2) * hbr
  have hf_scalar : f = 1 + (1 + u - 2 * v) / u := by
    rw [hf_formula, haN, haNcoord, haac, haad]
    have hcc : @inner ℝ V _ c c = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c
    have hdd : @inner ℝ V _ d d = ‖c‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq, ← hnormcd]
    have haa : @inner ℝ V _ a a = ‖c‖ ^ 2 := by
      rw [hACinner, hcc]
    rw [hcc, hdd, haa]
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr
      (vsub_ne_zero.mpr (hai_PCD.injective.ne (by decide : (1 : Fin 3) ≠ 0)))
    have hbr := hbase_relation
    field_simp [huv0, hu0, hcpos.ne']
    ring_nf at hbr ⊢
    linear_combination -(u + v) * hbr
  have hEFne : E ≠ F := by
    intro hEF
    have hvec : (1 - e) • a = (1 - f) • a := by rw [← hEv, ← hFv, hEF]
    have ha0 : a ≠ 0 := by
      intro ha
      apply (ne_of_gt hq)
      rw [← hACinner, ha, inner_zero_left]
    have hef : e = f := by
      have hz : (e - f) • a = 0 := by
        calc
          (e - f) • a = -((1 - e) • a - (1 - f) • a) := by module
          _ = 0 := by rw [hvec, sub_self, neg_zero]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right ha0)
    rw [he_scalar, hf_scalar] at hef
    have hfac : (u + v - 1) * (2 * u - 2 * v + 1) = 0 := by
      field_simp [hu0, hv1] at hef
      ring_nf at hef ⊢
      linear_combination hef
    rcases mul_eq_zero.mp hfac with hsum | hdiff
    · have : u = 1 - v := by linarith
      exact (ne_of_lt huvsum) this
    · have huvhalf : v - u = 1 / 2 := by linarith
      have hcenters : Γ.center -ᵥ Ω.center = (v - u) • (d - c) := by
        rw [← vsub_sub_vsub_cancel_right Γ.center Ω.center P₀, hNv, hMv]
        module
      have hAcoord : a = (2 * (1 - v)) • c + (2 * u) • d := by
        rw [hAv_final]
        rw [huvhalf]
        module
      have hEcommon : E ∈ Ω ∧ E ∈ Γ := ⟨EΩ, hEF ▸ FΓ⟩
      have hEinter := eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
        (Fact.out : finrank ℝ V = 2)
        ((Sphere.center_ne_iff_ne_of_mem AΩ AΓ).1 M_ne_N)
        A_ne_B AΩ BΩ hEcommon.1 AΓ BΓ hEcommon.2
      have hEB : E = B := hEinter.resolve_left E_ne_A
      have hBv : B -ᵥ P₀ = (1 - e) • a := by rw [← hEv, hEB]
      have hBA : B -ᵥ A = -e • a := by
        rw [← vsub_sub_vsub_cancel_right B A P₀, hBv]
        change (1 - e) • a - a = _
        module
      have horth := inner_vsub_vsub_of_mem_sphere_of_mem_sphere AΩ BΩ AΓ BΓ
      rw [hcenters, hBA, inner_smul_left, inner_smul_right] at horth
      have hadc : @inner ℝ V _ (d - c) a = 0 := by
        have horth' := horth
        norm_num at horth'
        rcases horth' with hvu0 | hezero | hadczero
        · exact False.elim (huv0 hvu0)
        · exact False.elim (he0 hezero)
        · exact hadczero
      have hcalc :
          2 * (u + v - 1) * (‖c‖ ^ 2 - @inner ℝ V _ c d) = 0 := by
        rw [hAcoord] at hadc
        simp only [inner_sub_left, inner_add_right, inner_smul_right] at hadc
        have hcc : @inner ℝ V _ c c = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c
        have hdd : @inner ℝ V _ d d = ‖c‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq, ← hnormcd]
        rw [hcc, hdd, hcdcomm] at hadc
        ring_nf at hadc ⊢
        exact hadc
      have huvsum_eq : u + v = 1 := by
        have := (mul_eq_zero.mp hcalc).resolve_right hqc0
        linarith
      linarith
  have affineIndependent_BEF : AffineIndependent ℝ ![B, E, F] := by
    apply affineIndependent_iff_not_collinear_set.mpr
    intro hcol
    have hBEFline : B ∈ line[ℝ, E, F] :=
      hcol.mem_affineSpan_of_mem_of_ne
        (by simp : E ∈ ({B, E, F} : Set Pt)) (by simp) (by simp) hEFne
    have hlineeq := affineSpan_pair_eq_of_mem_of_mem_of_ne Eline Fline hEFne
    have hBAP : B ∈ line[ℝ, A, P₀] := by
      change B ∈ line[ℝ, A, tACD.circumcenter]
      rw [← hlineeq]
      exact hBEFline
    have hBsecond := (Ω.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair AΩ hBAP).2 BΩ
    rcases hBsecond with hBA | hBsec
    · exact A_ne_B hBA.symm
    · have hEsecond := (Ω.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair AΩ Eline).2 EΩ
      rcases hEsecond with hEA | hEsec
      · exact E_ne_A hEA
      · have hBE : B = E := by rw [hBsec, hEsec]
        have hFsecond := (Γ.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair AΓ Fline).2 FΓ
        have hBΓsecond := (Γ.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair AΓ hBAP).2 BΓ
        rcases hFsecond with hFA | hFsec
        · exact F_ne_A hFA
        · rcases hBΓsecond with hBA' | hBsec'
          · exact A_ne_B hBA'.symm
          · apply hEFne
            rw [← hBE, hBsec', hFsec]
  refine ⟨affineIndependent_BEF, ?_⟩
  let tPMN : Triangle ℝ Pt :=
    ⟨![tACD.circumcenter, Ω.center, Γ.center], affineIndependent_PMN⟩
  have hH_MN := tPMN.inner_mongePoint_vsub_face_centroid_vsub
    (i₁ := (1 : Fin 3)) (i₂ := (2 : Fin 3))
  rw [show ({(1 : Fin 3), (2 : Fin 3)}ᶜ : Finset (Fin 3)) = {0} by decide,
    Finset.centroid_singleton] at hH_MN
  change @inner ℝ V _ (tPMN.orthocenter -ᵥ P₀)
    (Ω.center -ᵥ Γ.center) = 0 at hH_MN
  have hHcoord : ∃ h₁ h₂ : ℝ,
      tPMN.orthocenter -ᵥ P₀ = h₁ • c + h₂ • d :=
    affine_coordinates_of_independent hai_PCD
  obtain ⟨h₁, h₂, hHv⟩ := hHcoord
  rw [show Ω.center -ᵥ Γ.center = (v - u) • (c - d) by
    rw [← vsub_sub_vsub_cancel_right Ω.center Γ.center P₀, hMv, hNv]
    module] at hH_MN
  have hH_perp : @inner ℝ V _ (tPMN.orthocenter -ᵥ P₀) (c - d) = 0 := by
    rw [inner_smul_right] at hH_MN
    exact (mul_eq_zero.mp hH_MN).resolve_left huv0
  have hHeq : h₁ = h₂ := by
    rw [hHv, inner_add_left, inner_smul_left, inner_smul_left,
      inner_sub_right, inner_sub_right] at hH_perp
    simp only [starRingEnd_apply, star_trivial] at hH_perp
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← hnormcd, hcdcomm] at hH_perp
    have hz : (h₁ - h₂) * (‖c‖ ^ 2 - @inner ℝ V _ c d) = 0 := by
      ring_nf at hH_perp ⊢
      exact hH_perp
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hqc0)
  have hHv_eq : tPMN.orthocenter -ᵥ P₀ = h₂ • c + h₂ • d := by
    rw [hHv, hHeq]
  have hH_alt := tPMN.inner_mongePoint_vsub_face_centroid_vsub
    (i₁ := (0 : Fin 3)) (i₂ := (2 : Fin 3))
  rw [show ({(0 : Fin 3), (2 : Fin 3)}ᶜ : Finset (Fin 3)) = {1} by decide,
    Finset.centroid_singleton] at hH_alt
  change @inner ℝ V _ (tPMN.orthocenter -ᵥ Ω.center)
    (P₀ -ᵥ Γ.center) = 0 at hH_alt
  rw [show tPMN.orthocenter -ᵥ Ω.center =
      (tPMN.orthocenter -ᵥ P₀) - (Ω.center -ᵥ P₀) by
        exact (vsub_sub_vsub_cancel_right tPMN.orthocenter Ω.center P₀).symm,
    hHv_eq, hMv,
    show P₀ -ᵥ Γ.center = -((1 - v) • c + v • d) by rw [← hNv, neg_vsub_eq_vsub_rev]]
    at hH_alt
  simp only [inner_sub_left, inner_neg_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial] at hH_alt
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    ← hnormcd, hcdcomm] at hH_alt
  have hh₂_formula : h₂ = v - u := by
    have hsum0 : ‖c‖ ^ 2 + @inner ℝ V _ c d ≠ 0 := by
      intro hsum
      apply hgram0
      nlinarith
    have hprod :
        (h₂ - (v - u)) * (‖c‖ ^ 2 + @inner ℝ V _ c d) = 0 := by
      have hbr := hbase_relation
      ring_nf at hH_alt hbr ⊢
      linear_combination hbr - hH_alt
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum0)
  have hHv_final : tPMN.orthocenter -ᵥ P₀ =
      (v - u) • c + (v - u) • d := by
    rw [hHv_eq, hh₂_formula]
  have hBchord := inner_vsub_vsub_of_mem_sphere_of_mem_sphere AΩ BΩ AΓ BΓ
  have hBchord' : @inner ℝ V _ ((v - u) • (d - c)) ((B -ᵥ P₀) - a) = 0 := by
    simpa only [show Γ.center -ᵥ Ω.center = (v - u) • (d - c) by
      rw [← vsub_sub_vsub_cancel_right Γ.center Ω.center P₀, hNv, hMv]
      module,
      show B -ᵥ A = (B -ᵥ P₀) - a by
        dsimp only [a]
        exact (vsub_sub_vsub_cancel_right B A P₀).symm] using hBchord
  obtain ⟨b₁, b₂, hBv⟩ := affine_coordinates_of_independent
    (P := P₀) (C := C) (D := D) (X := B) hai_PCD
  change B -ᵥ P₀ = b₁ • c + b₂ • d at hBv
  have hb_diff : b₂ - b₁ = (u + v - 1) / (v - u) := by
    rw [hBv, hAv_final] at hBchord'
    simp only [inner_smul_left, inner_sub_left, inner_sub_right, inner_add_right,
      inner_smul_right, starRingEnd_apply, star_trivial] at hBchord'
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← hnormcd, hcdcomm] at hBchord'
    field_simp [huv0] at hBchord' ⊢
    ring_nf at hBchord' ⊢
    have hz :
        ((b₁ - b₂) * (v - u) + u + v - 1) *
          (‖c‖ ^ 2 - @inner ℝ V _ c d) = 0 := by
      ring_nf at hBchord' ⊢
      linear_combination -hBchord'
    have := (mul_eq_zero.mp hz).resolve_right hqc0
    linarith
  have hBΩeq := dist_center_eq_dist_center_of_mem_sphere AΩ BΩ
  have hBMv : B -ᵥ Ω.center =
      (b₁ - (1 - u)) • c + (b₂ - u) • d := by
    rw [← vsub_sub_vsub_cancel_right B Ω.center P₀, hBv, hMv]
    module
  have hAMv : A -ᵥ Ω.center =
      ((1 - v) / (v - u) - (1 - u)) • c +
        (u / (v - u) - u) • d := by
    rw [← vsub_sub_vsub_cancel_right A Ω.center P₀]
    change a - (Ω.center -ᵥ P₀) = _
    rw [hAv_final, hMv]
    module
  have hBinner :
      @inner ℝ V _ (B -ᵥ Ω.center) (B -ᵥ Ω.center) =
        @inner ℝ V _ (A -ᵥ Ω.center) (A -ᵥ Ω.center) := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hBΩeq]
  have hcc : @inner ℝ V _ c c = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c
  have hdd : @inner ℝ V _ d d = ‖c‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← hnormcd]
  have hBcoord := inner_coordinates
    (c := c) (d := d) (x := B -ᵥ Ω.center) (y := B -ᵥ Ω.center)
    (‖c‖ ^ 2) (@inner ℝ V _ c d)
    (b₁ - (1 - u)) (b₂ - u) (b₁ - (1 - u)) (b₂ - u)
    hcc hdd rfl hBMv hBMv
  have hAcoord := inner_coordinates
    (c := c) (d := d) (x := A -ᵥ Ω.center) (y := A -ᵥ Ω.center)
    (‖c‖ ^ 2) (@inner ℝ V _ c d)
    ((1 - v) / (v - u) - (1 - u)) (u / (v - u) - u)
    ((1 - v) / (v - u) - (1 - u)) (u / (v - u) - u)
    hcc hdd rfl hAMv hAMv
  rw [hBcoord, hAcoord] at hBinner
  have hb₂_expr : b₂ = b₁ + (u + v - 1) / (v - u) := by
    linarith [hb_diff]
  have hBinner' := hBinner
  rw [hb₂_expr] at hBinner'
  have hroot_factor :
      (b₁ * (v - u) - (1 - v)) *
          (b₁ * (v - u) - (v - 2 * u)) *
          (‖c‖ ^ 2 + @inner ℝ V _ c d) = 0 := by
    field_simp [huv0] at hBinner' ⊢
    ring_nf at hBinner' ⊢
    linear_combination hBinner' / 2
  have hsum0 : ‖c‖ ^ 2 + @inner ℝ V _ c d ≠ 0 := by
    intro hsum
    apply hgram0
    have hinner : @inner ℝ V _ c d = -‖c‖ ^ 2 := by linarith
    rw [hinner]
    ring
  have hroots := (mul_eq_zero.mp hroot_factor).resolve_right hsum0
  have hb₁_or : b₁ = (1 - v) / (v - u) ∨ b₁ = (v - 2 * u) / (v - u) := by
    rcases mul_eq_zero.mp hroots with hroot | hroot
    · left
      rw [eq_div_iff huv0]
      linarith
    · right
      rw [eq_div_iff huv0]
      linarith
  have hb₁_formula : b₁ = (v - 2 * u) / (v - u) := by
    rcases hb₁_or with hbA | hbB
    · exfalso
      apply A_ne_B
      have hb₂A : b₂ = u / (v - u) := by
        apply (eq_div_iff huv0).2
        have hbeq := hb_diff
        rw [hbA] at hbeq
        field_simp [huv0] at hbeq
        linarith
      apply vsub_left_cancel (p := P₀)
      rw [hBv, hbA, hb₂A]
      change A -ᵥ P₀ = _
      rw [show A -ᵥ P₀ = a by rfl, hAv_final]
    · exact hbB
  have hb₂_formula : b₂ = (2 * v - u - 1) / (v - u) := by
    rw [eq_div_iff huv0]
    field_simp [huv0] at hb_diff hb₁_formula
    linarith
  have hBv_final : B -ᵥ P₀ =
      ((v - 2 * u) / (v - u)) • c +
        ((2 * v - u - 1) / (v - u)) • d := by
    rw [hBv, hb₁_formula, hb₂_formula]
  let tBEF : Triangle ℝ Pt := ⟨![B, E, F], affineIndependent_BEF⟩
  let O : Pt := tBEF.circumcenter
  obtain ⟨o₁, o₂, hOv⟩ := affine_coordinates_of_independent
    (P := P₀) (C := C) (D := D) (X := O) hai_PCD
  have hEv_final : E -ᵥ P₀ =
      ((v - 2 * u) / (v - u)) • c +
        (u * (v - 2 * u) / ((1 - v) * (v - u))) • d := by
    rw [hEv, hAv_final, he_scalar]
    have hs1 : 1 - (1 + (2 * u - v) / (1 - v)) =
        (v - 2 * u) / (1 - v) := by field_simp [hv1]; ring
    rw [hs1]
    have hc : ((v - 2 * u) / (1 - v)) * ((1 - v) / (v - u)) =
        (v - 2 * u) / (v - u) := by field_simp [huv0, hv1]
    have hd : ((v - 2 * u) / (1 - v)) * (u / (v - u)) =
        u * (v - 2 * u) / ((1 - v) * (v - u)) := by
      field_simp [huv0, hv1]
    rw [smul_add, smul_smul, smul_smul, hc, hd]
  have hFv_final : F -ᵥ P₀ =
      ((1 - v) * (2 * v - u - 1) / (u * (v - u))) • c +
        ((2 * v - u - 1) / (v - u)) • d := by
    rw [hFv, hAv_final, hf_scalar]
    have hs1 : 1 - (1 + (1 + u - 2 * v) / u) =
        (2 * v - u - 1) / u := by field_simp [hu0]; ring
    rw [hs1]
    have hc : ((2 * v - u - 1) / u) * ((1 - v) / (v - u)) =
        (1 - v) * (2 * v - u - 1) / (u * (v - u)) := by
      field_simp [huv0, hu0]
    have hd : ((2 * v - u - 1) / u) * (u / (v - u)) =
        (2 * v - u - 1) / (v - u) := by field_simp [huv0, hu0]
    rw [smul_add, smul_smul, smul_smul, hc, hd]
  have hdistBOF : dist B O = dist F O := by
    exact (tBEF.dist_circumcenter_eq_circumradius 0).trans
      (tBEF.dist_circumcenter_eq_circumradius 2).symm
  have hdistBOE : dist B O = dist E O := by
    exact (tBEF.dist_circumcenter_eq_circumradius 0).trans
      (tBEF.dist_circumcenter_eq_circumradius 1).symm
  have hBOinner :
      @inner ℝ V _ (B -ᵥ O) (B -ᵥ O) =
        @inner ℝ V _ (F -ᵥ O) (F -ᵥ O) := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hdistBOF]
  have hBEinner :
      @inner ℝ V _ (B -ᵥ O) (B -ᵥ O) =
        @inner ℝ V _ (E -ᵥ O) (E -ᵥ O) := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hdistBOE]
  have hBOv : B -ᵥ O =
      (((v - 2 * u) / (v - u)) - o₁) • c +
        (((2 * v - u - 1) / (v - u)) - o₂) • d := by
    rw [← vsub_sub_vsub_cancel_right B O P₀, hBv_final, hOv]
    module
  have hEOv : E -ᵥ O =
      (((v - 2 * u) / (v - u)) - o₁) • c +
        ((u * (v - 2 * u) / ((1 - v) * (v - u))) - o₂) • d := by
    rw [← vsub_sub_vsub_cancel_right E O P₀, hEv_final, hOv]
    module
  have hFOv : F -ᵥ O =
      (((1 - v) * (2 * v - u - 1) / (u * (v - u))) - o₁) • c +
        (((2 * v - u - 1) / (v - u)) - o₂) • d := by
    rw [← vsub_sub_vsub_cancel_right F O P₀, hFv_final, hOv]
    module
  have hBOcoord := inner_coordinates
    (c := c) (d := d) (x := B -ᵥ O) (y := B -ᵥ O)
    (‖c‖ ^ 2) (@inner ℝ V _ c d)
    (((v - 2 * u) / (v - u)) - o₁) (((2 * v - u - 1) / (v - u)) - o₂)
    (((v - 2 * u) / (v - u)) - o₁) (((2 * v - u - 1) / (v - u)) - o₂)
    hcc hdd rfl hBOv hBOv
  have hEOcoord := inner_coordinates
    (c := c) (d := d) (x := E -ᵥ O) (y := E -ᵥ O)
    (‖c‖ ^ 2) (@inner ℝ V _ c d)
    (((v - 2 * u) / (v - u)) - o₁)
    ((u * (v - 2 * u) / ((1 - v) * (v - u))) - o₂)
    (((v - 2 * u) / (v - u)) - o₁)
    ((u * (v - 2 * u) / ((1 - v) * (v - u))) - o₂)
    hcc hdd rfl hEOv hEOv
  have hFOcoord := inner_coordinates
    (c := c) (d := d) (x := F -ᵥ O) (y := F -ᵥ O)
    (‖c‖ ^ 2) (@inner ℝ V _ c d)
    (((1 - v) * (2 * v - u - 1) / (u * (v - u))) - o₁)
    (((2 * v - u - 1) / (v - u)) - o₂)
    (((1 - v) * (2 * v - u - 1) / (u * (v - u))) - o₁)
    (((2 * v - u - 1) / (v - u)) - o₂)
    hcc hdd rfl hFOv hFOv
  rw [hBOcoord, hFOcoord] at hBOinner
  rw [hBOcoord, hEOcoord] at hBEinner
  have hsum_ne : u + v - 1 ≠ 0 := by
    intro hsum
    have huvsum_eq : u = 1 - v := by linarith
    exact (ne_of_lt huvsum) huvsum_eq
  have hwne : 2 * (v - u) - 1 ≠ 0 := by
    intro hw
    have hnum : 2 * u - v = -(1 - v) := by linarith
    have hezero : e = 0 := by
      rw [he_scalar, hnum, neg_div, div_self hv1]
      ring
    apply E_ne_A
    apply vsub_left_cancel (p := P₀)
    rw [hEv, hezero, sub_zero, one_smul]
  have hfacval : (u + v - 1) * (2 * u - 2 * v + 1) ≠ 0 := by
    apply mul_ne_zero hsum_ne
    intro hz
    apply hwne
    have hz' : 2 * u - 2 * v + 1 = 0 := hz
    linear_combination -hz'
  have hlin1num :
      (u + v - 1) * (2 * u - 2 * v + 1) *
        (2 * @inner ℝ V _ c d * o₂ * u ^ 2 -
          2 * @inner ℝ V _ c d * o₂ * u * v -
          2 * @inner ℝ V _ c d * u ^ 2 +
          4 * @inner ℝ V _ c d * u * v -
          2 * @inner ℝ V _ c d * u +
          2 * ‖c‖ ^ 2 * o₁ * u ^ 2 -
          2 * ‖c‖ ^ 2 * o₁ * u * v -
          2 * ‖c‖ ^ 2 * u ^ 2 +
          2 * ‖c‖ ^ 2 * u * v -
          ‖c‖ ^ 2 * u - 2 * ‖c‖ ^ 2 * v ^ 2 +
          3 * ‖c‖ ^ 2 * v - ‖c‖ ^ 2) = 0 := by
    have h := hBOinner
    field_simp [huv0, hu0] at h
    ring_nf at h ⊢
    linear_combination -h
  have hlin1 :
      2 * @inner ℝ V _ c d * o₂ * u ^ 2 -
          2 * @inner ℝ V _ c d * o₂ * u * v -
          2 * @inner ℝ V _ c d * u ^ 2 +
          4 * @inner ℝ V _ c d * u * v -
          2 * @inner ℝ V _ c d * u +
          2 * ‖c‖ ^ 2 * o₁ * u ^ 2 -
          2 * ‖c‖ ^ 2 * o₁ * u * v -
          2 * ‖c‖ ^ 2 * u ^ 2 +
          2 * ‖c‖ ^ 2 * u * v -
          ‖c‖ ^ 2 * u - 2 * ‖c‖ ^ 2 * v ^ 2 +
          3 * ‖c‖ ^ 2 * v - ‖c‖ ^ 2 = 0 := by
    exact (mul_eq_zero.mp hlin1num).resolve_left hfacval
  have hlin2num :
      (u + v - 1) * (2 * u - 2 * v + 1) *
        (2 * @inner ℝ V _ c d * o₁ * u * v -
          2 * @inner ℝ V _ c d * o₁ * u -
          2 * @inner ℝ V _ c d * o₁ * v ^ 2 +
          2 * @inner ℝ V _ c d * o₁ * v -
          4 * @inner ℝ V _ c d * u * v +
          4 * @inner ℝ V _ c d * u +
          2 * @inner ℝ V _ c d * v ^ 2 -
          2 * @inner ℝ V _ c d * v +
          2 * ‖c‖ ^ 2 * o₂ * u * v -
          2 * ‖c‖ ^ 2 * o₂ * u -
          2 * ‖c‖ ^ 2 * o₂ * v ^ 2 +
          2 * ‖c‖ ^ 2 * o₂ * v +
          2 * ‖c‖ ^ 2 * u ^ 2 -
          2 * ‖c‖ ^ 2 * u * v +
          ‖c‖ ^ 2 * u + 2 * ‖c‖ ^ 2 * v ^ 2 -
          3 * ‖c‖ ^ 2 * v + ‖c‖ ^ 2) = 0 := by
    have h := hBEinner
    field_simp [huv0, hv1] at h
    ring_nf at h ⊢
    linear_combination -h
  have hlin2 :
      2 * @inner ℝ V _ c d * o₁ * u * v -
          2 * @inner ℝ V _ c d * o₁ * u -
          2 * @inner ℝ V _ c d * o₁ * v ^ 2 +
          2 * @inner ℝ V _ c d * o₁ * v -
          4 * @inner ℝ V _ c d * u * v +
          4 * @inner ℝ V _ c d * u +
          2 * @inner ℝ V _ c d * v ^ 2 -
          2 * @inner ℝ V _ c d * v +
          2 * ‖c‖ ^ 2 * o₂ * u * v -
          2 * ‖c‖ ^ 2 * o₂ * u -
          2 * ‖c‖ ^ 2 * o₂ * v ^ 2 +
          2 * ‖c‖ ^ 2 * o₂ * v +
          2 * ‖c‖ ^ 2 * u ^ 2 -
          2 * ‖c‖ ^ 2 * u * v +
          ‖c‖ ^ 2 * u + 2 * ‖c‖ ^ 2 * v ^ 2 -
          3 * ‖c‖ ^ 2 * v + ‖c‖ ^ 2 = 0 := by
    exact (mul_eq_zero.mp hlin2num).resolve_left hfacval
  have hTv : ((v - u) • c + (v - u) • d) + (2 * (v - u) - 1) • a =
      ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u)) • c +
        (-(u ^ 2 + u - v ^ 2) / (v - u)) • d := by
    rw [hAv_final]
    have hc : (v - u) + (2 * (v - u) - 1) * ((1 - v) / (v - u)) =
        (u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) := by
      field_simp [huv0]
      ring
    have hd : (v - u) + (2 * (v - u) - 1) * (u / (v - u)) =
        -(u ^ 2 + u - v ^ 2) / (v - u) := by
      field_simp [huv0]
      ring
    rw [smul_add, smul_smul, smul_smul]
    calc
      _ = ((v - u) + (2 * (v - u) - 1) * ((1 - v) / (v - u))) • c +
          ((v - u) + (2 * (v - u) - 1) * (u / (v - u))) • d := by module
      _ = _ := by rw [hc, hd]
  let T : Pt := (2 * (v - u) - 1) • a +ᵥ tPMN.orthocenter
  have hTvP : T -ᵥ P₀ =
      ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u)) • c +
        (-(u ^ 2 + u - v ^ 2) / (v - u)) • d := by
    rw [show T -ᵥ P₀ = (tPMN.orthocenter -ᵥ P₀) +
      (2 * (v - u) - 1) • a by
        dsimp only [T]
        rw [vadd_vsub_assoc]
        abel, hHv_final]
    exact hTv
  have hTOv : T -ᵥ O =
      ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁) • c +
        (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂) • d := by
    rw [← vsub_sub_vsub_cancel_right T O P₀, hTvP, hOv]
    module
  have hTOrth : @inner ℝ V _ a (T -ᵥ O) = 0 := by
    rw [hAv_final, hTOv]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← hnormcd, hcdcomm]
    have hz :
        2 * u * (v - 1) * (v - u) ^ 2 * (
          (1 - v) / (v - u) *
              (‖c‖ ^ 2 *
                  ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁) +
                @inner ℝ V _ c d *
                  (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂)) +
            u / (v - u) *
              (@inner ℝ V _ c d *
                  ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁) +
                ‖c‖ ^ 2 *
                  (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂))) = 0 := by
      field_simp [huv0]
      ring_nf at hlin1 hlin2 hbase_relation ⊢
      linear_combination
        -((1 - v) ^ 2) * hlin1 + u ^ 2 * hlin2 -
          (u - v + 1) * (u + v - 1) ^ 2 * hbase_relation
    have hcoef : 2 * u * (v - 1) * (v - u) ^ 2 ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by linarith [hu]) (by linarith [hv]))
        (pow_ne_zero 2 huv0)
    have hzero := (mul_eq_zero.mp hz).resolve_left hcoef
    ring_nf at hzero ⊢
    exact hzero
  have hdistTB : dist T O = dist B O := by
    apply sq_eq_sq₀ dist_nonneg dist_nonneg |>.mp
    have hTOcoord := inner_coordinates
      (c := c) (d := d) (x := T -ᵥ O) (y := T -ᵥ O)
      (‖c‖ ^ 2) (@inner ℝ V _ c d)
      ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁)
      (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂)
      ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁)
      (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂)
      hcc hdd rfl hTOv hTOv
    rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, hTOcoord, hBOcoord]
    have hz : u * (u - v) ^ 2 * (v - 1) * (
        ‖c‖ ^ 2 *
            (((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁) *
                ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁) +
              (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂) *
                (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂)) +
          @inner ℝ V _ c d *
            (((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁) *
                (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂) +
              (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂) *
                ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁)) -
        (‖c‖ ^ 2 *
            (((v - 2 * u) / (v - u) - o₁) * ((v - 2 * u) / (v - u) - o₁) +
              ((2 * v - u - 1) / (v - u) - o₂) *
                ((2 * v - u - 1) / (v - u) - o₂)) +
          @inner ℝ V _ c d *
            (((v - 2 * u) / (v - u) - o₁) *
                ((2 * v - u - 1) / (v - u) - o₂) +
              ((2 * v - u - 1) / (v - u) - o₂) *
                ((v - 2 * u) / (v - u) - o₁)))) = 0 := by
      let L1 : ℝ :=
        2 * @inner ℝ V _ c d * o₂ * u ^ 2 -
          2 * @inner ℝ V _ c d * o₂ * u * v -
          2 * @inner ℝ V _ c d * u ^ 2 +
          4 * @inner ℝ V _ c d * u * v -
          2 * @inner ℝ V _ c d * u +
          2 * ‖c‖ ^ 2 * o₁ * u ^ 2 -
          2 * ‖c‖ ^ 2 * o₁ * u * v -
          2 * ‖c‖ ^ 2 * u ^ 2 +
          2 * ‖c‖ ^ 2 * u * v -
          ‖c‖ ^ 2 * u - 2 * ‖c‖ ^ 2 * v ^ 2 +
          3 * ‖c‖ ^ 2 * v - ‖c‖ ^ 2
      let L2 : ℝ :=
        2 * @inner ℝ V _ c d * o₁ * u * v -
          2 * @inner ℝ V _ c d * o₁ * u -
          2 * @inner ℝ V _ c d * o₁ * v ^ 2 +
          2 * @inner ℝ V _ c d * o₁ * v -
          4 * @inner ℝ V _ c d * u * v +
          4 * @inner ℝ V _ c d * u +
          2 * @inner ℝ V _ c d * v ^ 2 -
          2 * @inner ℝ V _ c d * v +
          2 * ‖c‖ ^ 2 * o₂ * u * v -
          2 * ‖c‖ ^ 2 * o₂ * u -
          2 * ‖c‖ ^ 2 * o₂ * v ^ 2 +
          2 * ‖c‖ ^ 2 * o₂ * v +
          2 * ‖c‖ ^ 2 * u ^ 2 -
          2 * ‖c‖ ^ 2 * u * v +
          ‖c‖ ^ 2 * u + 2 * ‖c‖ ^ 2 * v ^ 2 -
          3 * ‖c‖ ^ 2 * v + ‖c‖ ^ 2
      let L0 : ℝ := ‖c‖ ^ 2 * (1 - 2 * v + 2 * u * v) +
        2 * @inner ℝ V _ c d * u * (1 - v)
      have hL1 : L1 = 0 := by
        dsimp only [L1]
        exact hlin1
      have hL2 : L2 = 0 := by
        dsimp only [L2]
        exact hlin2
      have hL0 : L0 = 0 := by
        dsimp only [L0]
        exact hbase_relation
      calc
        u * (u - v) ^ 2 * (v - 1) *
            (‖c‖ ^ 2 *
                (((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁) *
                    ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁) +
                  (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂) *
                    (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂)) +
              @inner ℝ V _ c d *
                (((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁) *
                    (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂) +
                  (-(u ^ 2 + u - v ^ 2) / (v - u) - o₂) *
                    ((u ^ 2 - 2 * u - v ^ 2 + 3 * v - 1) / (v - u) - o₁)) -
            (‖c‖ ^ 2 *
                (((v - 2 * u) / (v - u) - o₁) * ((v - 2 * u) / (v - u) - o₁) +
                  ((2 * v - u - 1) / (v - u) - o₂) *
                    ((2 * v - u - 1) / (v - u) - o₂)) +
              @inner ℝ V _ c d *
                (((v - 2 * u) / (v - u) - o₁) *
                    ((2 * v - u - 1) / (v - u) - o₂) +
                  ((2 * v - u - 1) / (v - u) - o₂) *
                    ((v - 2 * u) / (v - u) - o₁)))) =
            (v - 1) * (u - v + 1) * (u + v - 1) * L1 -
              u * (u - v + 1) * (u + v - 1) * L2 +
              (u - v + 1) ^ 2 * (u + v - 1) ^ 2 * L0 := by
          dsimp only [L1, L2, L0]
          field_simp [huv0]
          ring
        _ = 0 := by rw [hL1, hL2, hL0]; ring
    have hcoef : u * (u - v) ^ 2 * (v - 1) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero hu0 (pow_ne_zero 2 (by linarith [huv]))) (by linarith [hv])
    have hzero := (mul_eq_zero.mp hz).resolve_left hcoef
    linear_combination hzero
  have Tmem : T ∈ tBEF.circumsphere := by
    rw [mem_sphere, Simplex.circumsphere_center, Simplex.circumsphere_radius,
      ← tBEF.dist_circumcenter_eq_circumradius 0]
    exact hdistTB
  have hTline : T ∈ AffineSubspace.mk' tPMN.orthocenter
      line[ℝ, A, P₀].direction := by
    rw [AffineSubspace.mem_mk']
    dsimp only [T]
    rw [vadd_vsub]
    apply Submodule.smul_mem
    exact AffineSubspace.vsub_mem_direction
      (left_mem_affineSpan_pair ℝ A P₀) (right_mem_affineSpan_pair ℝ A P₀)
  refine ⟨T, Tmem, hTline, ?_⟩
  intro X hX
  rw [Sphere.mem_orthRadius_iff_inner_left]
  rw [AffineSubspace.mem_mk'] at hX
  have hdir : ∃ r : ℝ, r • a = X -ᵥ tPMN.orthocenter := by
    have hx' := hX
    rw [show line[ℝ, A, P₀].direction = ℝ ∙ a by
      rw [direction_affineSpan, vectorSpan_pair, show A -ᵥ P₀ = a by rfl]] at hx'
    exact Submodule.mem_span_singleton.mp hx'
  obtain ⟨r, hr⟩ := hdir
  have hXT : X -ᵥ T = (r - (2 * (v - u) - 1)) • a := by
    rw [show X -ᵥ T = (X -ᵥ tPMN.orthocenter) -
      (T -ᵥ tPMN.orthocenter) by
        exact (vsub_sub_vsub_cancel_right X T tPMN.orthocenter).symm,
      ← hr]
    dsimp only [T]
    rw [vadd_vsub]
    module
  rw [hXT, inner_smul_left, Simplex.circumsphere_center, hTOrth, mul_zero]
