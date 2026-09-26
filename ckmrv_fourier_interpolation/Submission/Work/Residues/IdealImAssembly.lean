/-
# Proposition 3.8(2) of CKMRV for the ideal `𝓘_-`: the final dimension argument

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)), Proposition
3.8(2), for `𝓘_- = (S - I)R + (T - I)²R` (respectively `𝓘_+ = (S + I)R + (T - I)²R`) in
`R = ℂ[SL(2,ℤ)]` modulo the collapse ideal `(z-1)R`.

Given part (1) of the paper's Proposition — the images of `1, T, TS, S, ST, STS` are a basis of
`R/𝓘` — this file deduces part (2): the images of `1, T, TS` are a basis of `R/𝓘_-`.

The argument is the paper's:
* left multiplication by `S` is `1` modulo `𝓘_-` (and `-1` modulo `𝓘_+`), so the six elements
  `1, T, TS, S, ST, STS`, which span `R/𝓘`, reduce to `1, T, TS` modulo `𝓘_±`; hence
  `dim R/𝓘_± ≤ 3`;
* the diagonal map `R/𝓘 → R/𝓘_+ × R/𝓘_-` is injective because `𝓘_+ ∩ 𝓘_- = 𝓘`
  (`Work.Residues.idealI_eq_idealIp_inf_idealIm`), so `6 = dim R/𝓘 ≤ dim R/𝓘_+ + dim R/𝓘_- ≤ 6`
  and both dimensions are `3`;
* spanning by `3` elements plus `dim R/𝓘_- = 3` makes the images of `1, T, TS` a basis.
-/
import Mathlib
import Submission.Work.Residues.Basic
import Submission.Work.Residues.basis_quotient_IdealI

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Residues

open Work.Kernels

/-! ## Elementary manipulations in a quotient -/

private theorem mkQ_eq_of_sub_mem (p : Submodule ℂ R) {a b : R} (h : a - b ∈ p) :
    Submodule.mkQ p a = Submodule.mkQ p b := by
  have h0 : Submodule.mkQ p (a - b) = 0 := (Submodule.Quotient.mk_eq_zero p).mpr h
  rw [map_sub, sub_eq_zero] at h0
  exact h0

private theorem mkQ_eq_neg_of_add_mem (p : Submodule ℂ R) {a b : R} (h : a + b ∈ p) :
    Submodule.mkQ p a = -Submodule.mkQ p b := by
  have h0 : Submodule.mkQ p (a + b) = 0 := (Submodule.Quotient.mk_eq_zero p).mpr h
  rw [map_add] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-! ## The reductions of the six elements modulo `𝓘_±` -/

private theorem R_S_sub_one_mem_idealIm : (R_S - 1 : R) ∈ idealIm := by
  have h : (R_S - 1) * 1 ∈ Work.Kernels.IdealIm :=
    Work.Kernels.mem_span2.mpr ⟨1, 0, by rw [mul_zero, add_zero]⟩
  simpa using IdealIm_le_idealIm h

private theorem M6_four_sub_one_mem_idealIm : (M6 4 - M6 1 : R) ∈ idealIm := by
  have h : (R_S - 1) * R_T ∈ Work.Kernels.IdealIm :=
    Work.Kernels.mem_span2.mpr ⟨R_T, 0, by rw [mul_zero, add_zero]⟩
  have e : (R_S - 1) * R_T = (M6 4 - M6 1 : R) := by
    rw [M6_four, M6_one, sub_mul, one_mul]
  rw [← e]; exact IdealIm_le_idealIm h

private theorem M6_five_sub_two_mem_idealIm : (M6 5 - M6 2 : R) ∈ idealIm := by
  have h : (R_S - 1) * (R_T * R_S) ∈ Work.Kernels.IdealIm :=
    Work.Kernels.mem_span2.mpr ⟨R_T * R_S, 0, by rw [mul_zero, add_zero]⟩
  have e : (R_S - 1) * (R_T * R_S) = (M6 5 - M6 2 : R) := by
    rw [M6_five, M6_two, sub_mul, one_mul]
    simp [mul_assoc]
  rw [← e]; exact IdealIm_le_idealIm h

private theorem R_S_add_one_mem_idealIp : (R_S + 1 : R) ∈ idealIp := by
  have h : (R_S + 1) * 1 ∈ Work.Kernels.IdealIp :=
    Work.Kernels.mem_span2.mpr ⟨1, 0, by rw [mul_zero, add_zero]⟩
  simpa using IdealIp_le_idealIp h

private theorem M6_four_add_one_mem_idealIp : (M6 4 + M6 1 : R) ∈ idealIp := by
  have h : (R_S + 1) * R_T ∈ Work.Kernels.IdealIp :=
    Work.Kernels.mem_span2.mpr ⟨R_T, 0, by rw [mul_zero, add_zero]⟩
  have e : (R_S + 1) * R_T = (M6 4 + M6 1 : R) := by
    rw [M6_four, M6_one, add_mul, one_mul]
  rw [← e]; exact IdealIp_le_idealIp h

private theorem M6_five_add_two_mem_idealIp : (M6 5 + M6 2 : R) ∈ idealIp := by
  have h : (R_S + 1) * (R_T * R_S) ∈ Work.Kernels.IdealIp :=
    Work.Kernels.mem_span2.mpr ⟨R_T * R_S, 0, by rw [mul_zero, add_zero]⟩
  have e : (R_S + 1) * (R_T * R_S) = (M6 5 + M6 2 : R) := by
    rw [M6_five, M6_two, add_mul, one_mul]
    simp [mul_assoc]
  rw [← e]; exact IdealIp_le_idealIp h

/-! ## The images of `1, T, TS` and those of the six elements -/

/-- The images of `1, T, TS` in `R ⧸ 𝓘_-`. -/
private def vIm : Fin 3 → (R ⧸ idealIm) := fun i => Submodule.mkQ idealIm (M3 i)

/-- The images of `1, T, TS` in `R ⧸ 𝓘_+`. -/
private def vIp : Fin 3 → (R ⧸ idealIp) := fun i => Submodule.mkQ idealIp (M3 i)

private theorem mkQ_Im_M6_mem (i : Fin 6) :
    Submodule.mkQ idealIm (M6 i) ∈ Submodule.span ℂ (Set.range vIm) := by
  fin_cases i
  · show Submodule.mkQ idealIm (M6 (0 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIm)
    have h : Submodule.mkQ idealIm (M6 (0 : Fin 6)) = vIm 0 := by
      change Submodule.mkQ idealIm (M6 0) = Submodule.mkQ idealIm (M3 0)
      rw [M6_zero, M3_zero]
    rw [h]; exact Submodule.subset_span ⟨0, rfl⟩
  · show Submodule.mkQ idealIm (M6 (1 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIm)
    have h : Submodule.mkQ idealIm (M6 (1 : Fin 6)) = vIm 1 := by
      change Submodule.mkQ idealIm (M6 1) = Submodule.mkQ idealIm (M3 1)
      rw [M6_one, M3_one]
    rw [h]; exact Submodule.subset_span ⟨1, rfl⟩
  · show Submodule.mkQ idealIm (M6 (2 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIm)
    have h : Submodule.mkQ idealIm (M6 (2 : Fin 6)) = vIm 2 := by
      change Submodule.mkQ idealIm (M6 2) = Submodule.mkQ idealIm (M3 2)
      rw [M6_two, M3_two]
    rw [h]; exact Submodule.subset_span ⟨2, rfl⟩
  · show Submodule.mkQ idealIm (M6 (3 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIm)
    have h : Submodule.mkQ idealIm (M6 (3 : Fin 6)) = Submodule.mkQ idealIm (M6 0) :=
      mkQ_eq_of_sub_mem idealIm (by rw [M6_three, M6_zero]; exact R_S_sub_one_mem_idealIm)
    have h2 : Submodule.mkQ idealIm (M6 (0 : Fin 6)) = vIm 0 := by
      change Submodule.mkQ idealIm (M6 0) = Submodule.mkQ idealIm (M3 0)
      rw [M6_zero, M3_zero]
    rw [h, h2]; exact Submodule.subset_span ⟨0, rfl⟩
  · show Submodule.mkQ idealIm (M6 (4 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIm)
    have h : Submodule.mkQ idealIm (M6 (4 : Fin 6)) = Submodule.mkQ idealIm (M6 1) :=
      mkQ_eq_of_sub_mem idealIm M6_four_sub_one_mem_idealIm
    have h2 : Submodule.mkQ idealIm (M6 (1 : Fin 6)) = vIm 1 := by
      change Submodule.mkQ idealIm (M6 1) = Submodule.mkQ idealIm (M3 1)
      rw [M6_one, M3_one]
    rw [h, h2]; exact Submodule.subset_span ⟨1, rfl⟩
  · show Submodule.mkQ idealIm (M6 (5 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIm)
    have h : Submodule.mkQ idealIm (M6 (5 : Fin 6)) = Submodule.mkQ idealIm (M6 2) :=
      mkQ_eq_of_sub_mem idealIm M6_five_sub_two_mem_idealIm
    have h2 : Submodule.mkQ idealIm (M6 (2 : Fin 6)) = vIm 2 := by
      change Submodule.mkQ idealIm (M6 2) = Submodule.mkQ idealIm (M3 2)
      rw [M6_two, M3_two]
    rw [h, h2]; exact Submodule.subset_span ⟨2, rfl⟩

private theorem mkQ_Ip_M6_mem (i : Fin 6) :
    Submodule.mkQ idealIp (M6 i) ∈ Submodule.span ℂ (Set.range vIp) := by
  fin_cases i
  · show Submodule.mkQ idealIp (M6 (0 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIp)
    have h : Submodule.mkQ idealIp (M6 (0 : Fin 6)) = vIp 0 := by
      change Submodule.mkQ idealIp (M6 0) = Submodule.mkQ idealIp (M3 0)
      rw [M6_zero, M3_zero]
    rw [h]; exact Submodule.subset_span ⟨0, rfl⟩
  · show Submodule.mkQ idealIp (M6 (1 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIp)
    have h : Submodule.mkQ idealIp (M6 (1 : Fin 6)) = vIp 1 := by
      change Submodule.mkQ idealIp (M6 1) = Submodule.mkQ idealIp (M3 1)
      rw [M6_one, M3_one]
    rw [h]; exact Submodule.subset_span ⟨1, rfl⟩
  · show Submodule.mkQ idealIp (M6 (2 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIp)
    have h : Submodule.mkQ idealIp (M6 (2 : Fin 6)) = vIp 2 := by
      change Submodule.mkQ idealIp (M6 2) = Submodule.mkQ idealIp (M3 2)
      rw [M6_two, M3_two]
    rw [h]; exact Submodule.subset_span ⟨2, rfl⟩
  · show Submodule.mkQ idealIp (M6 (3 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIp)
    have h : Submodule.mkQ idealIp (M6 (3 : Fin 6)) = -Submodule.mkQ idealIp (M6 0) :=
      mkQ_eq_neg_of_add_mem idealIp (by rw [M6_three, M6_zero]; exact R_S_add_one_mem_idealIp)
    have h2 : Submodule.mkQ idealIp (M6 (0 : Fin 6)) = vIp 0 := by
      change Submodule.mkQ idealIp (M6 0) = Submodule.mkQ idealIp (M3 0)
      rw [M6_zero, M3_zero]
    rw [h, h2]; exact Submodule.neg_mem _ (Submodule.subset_span ⟨0, rfl⟩)
  · show Submodule.mkQ idealIp (M6 (4 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIp)
    have h : Submodule.mkQ idealIp (M6 (4 : Fin 6)) = -Submodule.mkQ idealIp (M6 1) :=
      mkQ_eq_neg_of_add_mem idealIp M6_four_add_one_mem_idealIp
    have h2 : Submodule.mkQ idealIp (M6 (1 : Fin 6)) = vIp 1 := by
      change Submodule.mkQ idealIp (M6 1) = Submodule.mkQ idealIp (M3 1)
      rw [M6_one, M3_one]
    rw [h, h2]; exact Submodule.neg_mem _ (Submodule.subset_span ⟨1, rfl⟩)
  · show Submodule.mkQ idealIp (M6 (5 : Fin 6)) ∈ Submodule.span ℂ (Set.range vIp)
    have h : Submodule.mkQ idealIp (M6 (5 : Fin 6)) = -Submodule.mkQ idealIp (M6 2) :=
      mkQ_eq_neg_of_add_mem idealIp M6_five_add_two_mem_idealIp
    have h2 : Submodule.mkQ idealIp (M6 (2 : Fin 6)) = vIp 2 := by
      change Submodule.mkQ idealIp (M6 2) = Submodule.mkQ idealIp (M3 2)
      rw [M6_two, M3_two]
    rw [h, h2]; exact Submodule.neg_mem _ (Submodule.subset_span ⟨2, rfl⟩)

/-! ## Part (2) for `𝓘_-` from part (1) -/

/-- **Paper Proposition 3.8(2)** for `𝓘_-`: if the images of `1, T, TS, S, ST, STS` are a basis
of `R/𝓘`, then the images of `1, T, TS` are a basis of `R/𝓘_-`. -/
theorem basis_IdealIm_of_basis_IdealI
    (hI : ∃ b : Module.Basis (Fin 6) ℂ (Work.Kernels.R ⧸ Work.Residues.idealI),
      ∀ i, b i = Submodule.mkQ Work.Residues.idealI (Work.Residues.M6 i)) :
    ∃ b : Module.Basis (Fin 3) ℂ (Work.Kernels.R ⧸ Work.Residues.idealIm),
      ∀ i, b i = Submodule.mkQ Work.Residues.idealIm (Work.Residues.M3 i) := by
  obtain ⟨b, hb⟩ := hI
  -- Reduction of an arbitrary element of `R` to the basis `M6` modulo `𝓘`, hence modulo
  -- any larger ideal.
  have reduce_repr : ∀ (p : Submodule ℂ R) (hp : idealI ≤ p) (r : R),
      Submodule.mkQ p r =
        ∑ i : Fin 6, (b.repr (Submodule.mkQ idealI r)) i • Submodule.mkQ p (M6 i) := by
    intro p hp r
    set c : Fin 6 →₀ ℂ := b.repr (Submodule.mkQ idealI r) with hc
    have hX : Submodule.mkQ idealI (∑ i, c i • M6 i) = Submodule.mkQ idealI r := by
      rw [map_sum]
      have hterm : ∀ i, Submodule.mkQ idealI (c i • M6 i) = c i • b i :=
        fun i => by rw [map_smul, ← hb i]
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      simpa [hc] using Module.Basis.sum_repr b (Submodule.mkQ idealI r)
    have hmem : r - ∑ i, c i • M6 i ∈ idealI := by
      have key : Submodule.mkQ idealI (r - ∑ i, c i • M6 i) = 0 := by
        rw [map_sub, hX, sub_self]
      exact (Submodule.Quotient.mk_eq_zero idealI).mp key
    have hsub : Submodule.mkQ p (r - ∑ i, c i • M6 i) = 0 :=
      (Submodule.Quotient.mk_eq_zero p).mpr (hp hmem)
    rw [map_sub, sub_eq_zero] at hsub
    rw [hsub, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  -- The images of `M6` span the two quotients.
  have hspan_m : Submodule.span ℂ (Set.range vIm) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective idealIm y
    rw [reduce_repr idealIm idealI_le_idealIm r]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (mkQ_Im_M6_mem i))
  have hspan_p : Submodule.span ℂ (Set.range vIp) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective idealIp y
    rw [reduce_repr idealIp idealI_le_idealIp r]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (mkQ_Ip_M6_mem i))
  -- Finiteness and the upper bounds `dim R/𝓘_± ≤ 3`.
  haveI hfin_m : Module.Finite ℂ (R ⧸ idealIm) :=
    ⟨by rw [← hspan_m]; exact Submodule.fg_span (Set.finite_range vIm)⟩
  haveI hfin_p : Module.Finite ℂ (R ⧸ idealIp) :=
    ⟨by rw [← hspan_p]; exact Submodule.fg_span (Set.finite_range vIp)⟩
  have hle_m : Module.finrank ℂ (R ⧸ idealIm) ≤ 3 := by
    have h1 := finrank_range_le_card (R := ℂ) vIm
    rw [Set.finrank, hspan_m] at h1
    simpa using h1
  have hle_p : Module.finrank ℂ (R ⧸ idealIp) ≤ 3 := by
    have h1 := finrank_range_le_card (R := ℂ) vIp
    rw [Set.finrank, hspan_p] at h1
    simpa using h1
  -- The diagonal map `R ⧸ 𝓘 → R ⧸ 𝓘_+ × R ⧸ 𝓘_-` is injective.
  let ψ : (R ⧸ idealI) →ₗ[ℂ] ((R ⧸ idealIp) × (R ⧸ idealIm)) :=
    Submodule.liftQ idealI (LinearMap.prod (Submodule.mkQ idealIp) (Submodule.mkQ idealIm)) (by
      intro x hx
      rw [LinearMap.mem_ker]
      exact Prod.ext ((Submodule.Quotient.mk_eq_zero idealIp).mpr (idealI_le_idealIp hx))
        ((Submodule.Quotient.mk_eq_zero idealIm).mpr (idealI_le_idealIm hx)))
  have hψ_inj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective idealI y
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply] at hy
    have hy' : (Submodule.mkQ idealIp r, Submodule.mkQ idealIm r) = (0, 0) := hy
    have h1 : Submodule.mkQ idealIp r = 0 := congrArg Prod.fst hy'
    have h2 : Submodule.mkQ idealIm r = 0 := congrArg Prod.snd hy'
    refine (Submodule.Quotient.mk_eq_zero idealI).mpr ?_
    rw [idealI_eq_idealIp_inf_idealIm]
    exact ⟨(Submodule.Quotient.mk_eq_zero idealIp).mp h1,
      (Submodule.Quotient.mk_eq_zero idealIm).mp h2⟩
  -- Dimensions: `6 = dim R/𝓘 ≤ dim R/𝓘_+ + dim R/𝓘_- ≤ 3 + 3`.
  have hfin_A : Module.finrank ℂ (R ⧸ idealI) = 6 := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hfin_M : Module.finrank ℂ (R ⧸ idealIm) = 3 := by
    have h := LinearMap.finrank_le_finrank_of_injective (R := ℂ) hψ_inj
    rw [hfin_A, Module.finrank_prod] at h
    omega
  -- Hence `vIm` is a basis of `R ⧸ 𝓘_-`.
  have hLI : LinearIndependent ℂ vIm := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card (Fin 3) = Module.finrank ℂ (↥(Submodule.span ℂ (Set.range vIm)))
    rw [hspan_m, (Submodule.topEquiv (R := ℂ)).finrank_eq, hfin_M, Fintype.card_fin]
  have hsp : (⊤ : Submodule ℂ (R ⧸ idealIm)) ≤ Submodule.span ℂ (Set.range vIm) := by
    rw [hspan_m]
  exact ⟨Module.Basis.mk hLI hsp, fun i => Module.Basis.mk_apply hLI hsp i⟩

end Work.Residues
