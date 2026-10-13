import Submission.Work.DSM2p.N8aux2

namespace Work.DSM2p

/-- **`A'_F = pIntClosure p (CSAlgOne A p ϖ₀ F)` is `A`-flat.**

`A'_F` is the union (over `m`) of the `p`-integral closures of `Λ[F(T)/ϖ₀^{m+1}]`
(`N8a_CSAlgOne_eq_iSup` + `pIntClosure_iSup`), and each of these stages is `A`-flat by
`N8_stage_flat`; a directed union of flat modules is flat (`flat_iSup_subring_of_flat`). -/
theorem N8_flat_pIntClosure_CSAlgOne (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (hF : F.Monic) :
    Module.Flat A ↥(pIntClosure p (CSAlgOne A p (P.ϖ 0) F)) := by
  classical
  have hstep : ∀ m : ℕ, (Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring ≤
      (Algebra.adjoin (Lam1 A p) {yF A p P F ((m + 1) + 1)}).toSubring := by
    intro m x hx
    rw [Subalgebra.mem_toSubring] at hx ⊢
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_) hx
    rw [yF_succ A p P F (m + 1)]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_singleton _))
      (Subalgebra.algebraMap_mem _ _)
  have hmonoAd : Monotone (fun m : ℕ =>
      (Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring) :=
    monotone_nat_of_le_succ hstep
  have hmonoSup : Monotone (fun m : ℕ => pIntClosure p
      ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)) :=
    fun a b hab => pIntClosure_mono p (hmonoAd hab)
  have hsub : pIntClosure p (CSAlgOne A p (P.ϖ 0) F) =
      ⨆ m : ℕ, pIntClosure p ((Algebra.adjoin (Lam1 A p)
        {yF A p P F (m + 1)}).toSubring) := by
    rw [N8a_CSAlgOne_eq_iSup A p (P.ϖ 0) F]
    exact pIntClosure_iSup p
      (fun m : ℕ => (Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring) hmonoAd
  have hcomp : ∀ m : ℕ, (Subring.subtype (pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring))).comp
        (algebraMap A ↥(pIntClosure p
          ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)))
      = (algebraMap A (Lam1Loc A p (P.ϖ 0))) := by
    intro m
    apply RingHom.ext
    intro a
    exact (IsScalarTower.algebraMap_apply A (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) a).symm
  have hcomp' : (Subring.subtype (⨆ m : ℕ, pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring))).comp
        (algebraMap A ↥(⨆ m : ℕ, pIntClosure p
          ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)))
      = (algebraMap A (Lam1Loc A p (P.ϖ 0))) := by
    apply RingHom.ext
    intro a
    exact (IsScalarTower.algebraMap_apply A (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) a).symm
  have hsup : Module.Flat A ↥(⨆ m : ℕ, pIntClosure p
      ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)) :=
    flat_iSup_subring_of_flat hmonoSup hcomp hcomp'
      (fun m => N8_stage_flat A p P F hF (m + 1) (Nat.succ_le_succ (Nat.zero_le m)))
  haveI : Module.Flat A ↥(⨆ m : ℕ, pIntClosure p
      ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)) := hsup
  have hmemL : ∀ z : ↥(⨆ m : ℕ, pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)),
      ((z : Lam1Loc A p (P.ϖ 0)) ∈ pIntClosure p (CSAlgOne A p (P.ϖ 0) F)) :=
    fun z => le_of_eq hsub.symm z.2
  have hmemR : ∀ z : ↥(pIntClosure p (CSAlgOne A p (P.ϖ 0) F)),
      ((z : Lam1Loc A p (P.ϖ 0)) ∈ ⨆ m : ℕ, pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)) :=
    fun z => le_of_eq hsub z.2
  let toF : ↥(⨆ m : ℕ, pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)) →
      ↥(pIntClosure p (CSAlgOne A p (P.ϖ 0) F)) :=
    fun z => Subtype.mk (z : Lam1Loc A p (P.ϖ 0)) (hmemL z)
  let invF : ↥(pIntClosure p (CSAlgOne A p (P.ϖ 0) F)) →
      ↥(⨆ m : ℕ, pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)) :=
    fun z => Subtype.mk (z : Lam1Loc A p (P.ϖ 0)) (hmemR z)
  have hsmul : ∀ (a : A) (z : ↥(⨆ m : ℕ, pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring))),
      ((a • z : ↥(⨆ m : ℕ, pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring))) :
          Lam1Loc A p (P.ϖ 0)) =
      ((a • toF z : ↥(pIntClosure p (CSAlgOne A p (P.ϖ 0) F))) : Lam1Loc A p (P.ϖ 0)) := by
    intro a z
    rw [Algebra.smul_def, Algebra.smul_def]
    show (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
            (algebraMap A (Lam1 A p) a)) * (z : Lam1Loc A p (P.ϖ 0)) =
        (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
          (algebraMap A (Lam1 A p) a)) * (z : Lam1Loc A p (P.ϖ 0))
    rfl
  let e : ↥(⨆ m : ℕ, pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)) ≃ₗ[A]
      ↥(pIntClosure p (CSAlgOne A p (P.ϖ 0) F)) :=
    show ↥(⨆ m : ℕ, pIntClosure p
          ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)) ≃ₗ[A]
        ↥(pIntClosure p (CSAlgOne A p (P.ϖ 0) F)) from
      { toFun := toF, invFun := invF, left_inv := fun _ => Subtype.ext rfl,
        right_inv := fun _ => Subtype.ext rfl, map_add' := fun _ _ => Subtype.ext rfl,
        map_smul' := fun a z => Subtype.ext (hsmul a z) }
  exact Module.Flat.of_linearEquiv e.symm

end Work.DSM2p
