/-
AREA RESOL — naturality of the canonical map out of a (mapping) telescope.

Given two sequences `P, P'` of cochain complexes with transition maps `t, t'`, a map of towers
`g : ∀ n, P n ⟶ P' n` inducing a map `S = ∐ g` of the coproducts that commutes with the
`telD = 1 - shift` differentials, and compatible cocones `f : P n ⟶ K`, `f' : P' n ⟶ K'` together
with `u : K ⟶ K'` and `g n ≫ f' n = f n ≫ u`, the canonical map `telDesc P t K f hf` out of the
telescope is natural:

`telDesc P t K f hf ≫ u = mappingCone.map (telD P t) (telD P' t') S S hcomm ≫ telDesc P' t' K' f' hf'`.

The two maps agree because `mappingCone.ext_from` detects maps out of a mapping cone by their
composites with `inl` and `inr`; at each degree `p` the `inl`-composite of both sides vanishes
(the `inl`-component of `telDesc` is the zero cochain) and the `inr`-composites are
`coconeMap P f ≫ u` resp. `S ≫ coconeMap P' f'`, which agree by `hgu` (the coproducts are
tested against the `Sigma.ι`'s).
-/
import Mathlib
import Submission.Work.RESOL.Telescope

open CategoryTheory Limits

namespace Work.RESOL

theorem telDesc_natural (P P' : ℕ → Work.RESOL.Cpx)
    [CategoryTheory.Limits.HasCoproduct P] [CategoryTheory.Limits.HasCoproduct P']
    (t : ∀ n : ℕ, P n ⟶ P (n+1)) (t' : ∀ n : ℕ, P' n ⟶ P' (n+1))
    (K K' : Work.RESOL.Cpx) (f : ∀ n : ℕ, P n ⟶ K) (f' : ∀ n : ℕ, P' n ⟶ K')
    (hf : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (t n) (f (n+1)) = f n)
    (hf' : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (t' n) (f' (n+1)) = f' n)
    (g : ∀ n : ℕ, P n ⟶ P' n)
    (hcomm : CategoryTheory.CategoryStruct.comp (Work.RESOL.telD P t)
        (CategoryTheory.Limits.Sigma.desc (fun n : ℕ => CategoryTheory.CategoryStruct.comp (g n) (CategoryTheory.Limits.Sigma.ι P' n))) =
      CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.Sigma.desc (fun n : ℕ => CategoryTheory.CategoryStruct.comp (g n) (CategoryTheory.Limits.Sigma.ι P' n)))
        (Work.RESOL.telD P' t'))
    (u : K ⟶ K')
    (hgu : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (g n) (f' n) =
      CategoryTheory.CategoryStruct.comp (f n) u) :
    CategoryTheory.CategoryStruct.comp (Work.RESOL.telDesc P t K f hf) u =
      CategoryTheory.CategoryStruct.comp
        (CochainComplex.mappingCone.map (Work.RESOL.telD P t) (Work.RESOL.telD P' t')
          (CategoryTheory.Limits.Sigma.desc (fun n : ℕ =>
            CategoryTheory.CategoryStruct.comp (g n) (CategoryTheory.Limits.Sigma.ι P' n)))
          (CategoryTheory.Limits.Sigma.desc (fun n : ℕ =>
            CategoryTheory.CategoryStruct.comp (g n) (CategoryTheory.Limits.Sigma.ι P' n))) hcomm)
        (Work.RESOL.telDesc P' t' K' f' hf') := by
  -- the map `S : ∐ n, P n ⟶ ∐ n, P' n` induced by `g`
  have hA : Sigma.desc (fun n : ℕ => g n ≫ Sigma.ι P' n) ≫ coconeMap P' f' =
      coconeMap P f ≫ u := by
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, ← Category.assoc, Sigma.ι_comp_desc]
    rw [Category.assoc, Sigma_ι_coconeMap, Sigma_ι_coconeMap, hgu n]
  -- unfold the two `telDesc`'s and the cone map into `mappingCone.desc`/`mappingCone.map`
  dsimp only [telDesc, tel, CochainComplex.mappingCone.map]
  apply HomologicalComplex.Hom.ext
  funext p
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  conv_rhs => rw [CochainComplex.mappingCone.desc_f _ _ _ _ p (p+1) rfl]
  conv_lhs => rw [CochainComplex.mappingCone.desc_f _ _ _ _ p (p+1) rfl]
  -- the degreewise form of `hA`
  have hAu : (Sigma.desc (fun n : ℕ => g n ≫ Sigma.ι P' n)).f p ≫ (coconeMap P' f').f p =
      (coconeMap P f).f p ≫ u.f p := by
    have := congrArg (fun m => m.f p) hA
    simpa only [HomologicalComplex.comp_f] using this
  -- expand the `inl`/`inr` components of the cone map and of `telDesc`, and cancel
  simp only [Preadditive.add_comp, Category.assoc,
    CochainComplex.HomComplex.Cochain.zero_v,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
    CochainComplex.mappingCone.inl_v_desc_f,
    CochainComplex.mappingCone.inr_f_desc_f, zero_comp, comp_zero]
  rw [hAu]

end Work.RESOL
