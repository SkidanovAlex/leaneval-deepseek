import ChallengeDeps
import Submission.StarQuotient
import Submission.E8Weights
import Mathlib.Algebra.Lie.SerreConstruction
import Submission.Commons.Algebra.Lie.SerreConstruction.liftOfSerrePresentation
set_option backward.isDefEq.respectTransparency false
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

noncomputable section
open scoped BigOperators

namespace Submission.VermaNonzero

open Submission.StarQuotient
open Submission.StarModule

/-- The Cartan matrix of `e₈`. -/
abbrev E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

lemma E8_symm : ∀ i j : Fin 8, E8 i j = E8 j i := by decide

lemma E8_diag : ∀ i : Fin 8, E8 i i = 2 := by decide

lemma E8_offdiag : ∀ i j : Fin 8, i ≠ j → E8 i j = 0 ∨ E8 i j = -1 := by decide

/-- The universal property of the Serre presentation applied to the ⋆-operators on `V = A/J`. -/
noncomputable def actExists (lam : Fin 8 → ℂ) :
    ∃ φ : LieAlgebra.e₈ ℂ →ₗ⁅ℂ⁆ Module.End ℂ (V E8),
      (∀ i, φ (Submission.E8Weights.SerreH i) = Hbar E8 lam i) ∧
      (∀ i, φ (Submission.E8Weights.SerreE i) = Ebar E8 lam i) ∧
      (∀ i, φ (Submission.E8Weights.SerreF i) = Lbar E8 i) :=
  Commons.Algebra.Lie.SerreConstruction.liftOfSerrePresentation (R := ℂ) (B := Fin 8)
    CartanMatrix.E₈ (Hbar E8 lam) (Ebar E8 lam) (Lbar E8)
    (fun i j => lie_Hbar_Hbar E8 lam i j)
    (fun i j => lie_Hbar_Ebar E8 lam i j)
    (fun i j => lie_Hbar_Lbar E8 lam i j)
    (fun i j => lie_Ebar_Lbar E8 lam i j)
    (fun i j => adE_zero E8 lam i j E8_symm E8_diag E8_offdiag)
    (fun i j => adF_zero E8 i j E8_symm E8_diag E8_offdiag)

/-- The `e₈`-action on the quotient `V = A/J`, obtained from the universal property of the Serre
presentation. -/
noncomputable def act (lam : Fin 8 → ℂ) : LieAlgebra.e₈ ℂ →ₗ⁅ℂ⁆ Module.End ℂ (V E8) :=
  (actExists lam).choose

lemma act_H (lam : Fin 8 → ℂ) (i : Fin 8) :
    act lam (Submission.E8Weights.SerreH i) = Hbar E8 lam i :=
  (actExists lam).choose_spec.1 i

lemma act_E (lam : Fin 8 → ℂ) (i : Fin 8) :
    act lam (Submission.E8Weights.SerreE i) = Ebar E8 lam i :=
  (actExists lam).choose_spec.2.1 i

lemma act_F (lam : Fin 8 → ℂ) (i : Fin 8) :
    act lam (Submission.E8Weights.SerreF i) = Lbar E8 i :=
  (actExists lam).choose_spec.2.2 i

/-- `V` is a Lie module of `e₈` through `act`. -/
noncomputable def lieRingModule (lam : Fin 8 → ℂ) :
    LieRingModule (LieAlgebra.e₈ ℂ) (V E8) where
  bracket x m := act lam x m
  add_lie x y m := by
    show act lam (x + y) m = act lam x m + act lam y m
    rw [map_add]; rfl
  lie_add x m n := by
    show act lam x (m + n) = act lam x m + act lam x n
    rw [map_add]
  leibniz_lie x y m := by
    show act lam x (act lam y m) = act lam (⁅x, y⁆) m + act lam y (act lam x m)
    rw [LieHom.map_lie]
    rw [show (⁅act lam x, act lam y⁆ : Module.End ℂ (V E8))
        = (act lam x).comp (act lam y) - (act lam y).comp (act lam x) from rfl]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    abel

noncomputable def lieModule (lam : Fin 8 → ℂ) :
    @LieModule ℂ (LieAlgebra.e₈ ℂ) (V E8) _ _ _ _ _ (lieRingModule lam) := by
  letI := lieRingModule lam
  exact
  { smul_lie := by
      intro t x m
      show act lam (t • x) m = t • act lam x m
      rw [map_smul]
      rfl
    lie_smul := by
      intro t x m
      show act lam x (t • m) = t • act lam x m
      exact (act lam x).map_smul t m }

/-! ## Non-vanishing -/

/-- The augmentation (counit) of the free monoid. -/
def counitHom : FreeMonoid (Fin 8) →* ℂ := by
  classical
  exact
    { toFun := fun w => if w = 1 then 1 else 0
      map_one' := if_pos rfl
      map_mul' := by
        intro a b
        by_cases ha : a = 1
        · subst ha; rw [one_mul, if_pos rfl, one_mul]
        · have hab : ¬(a * b = 1) := fun h => ha (by
            have h2 : (a * b).length = (1 : FreeMonoid (Fin 8)).length := by rw [h]
            rw [FreeMonoid.length_mul, FreeMonoid.length_one] at h2
            exact FreeMonoid.length_eq_zero.mp (by omega))
          rw [if_neg ha, if_neg hab, zero_mul] }

/-- The augmentation `FA → ℂ` of the free algebra: the algebra hom mapping each generator to `0`. -/
def aug : FA (Fin 8) →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ (FreeMonoid (Fin 8)) counitHom

lemma ofList_eq_one_iff {v : List (Fin 8)} : FreeMonoid.ofList v = 1 ↔ v = [] := by
  constructor
  · intro h
    have := congrArg FreeMonoid.toList h
    simpa using this
  · intro h; subst h; exact FreeMonoid.ofList_nil

lemma aug_wordElt (v : List (Fin 8)) : aug (wordElt v) = if v = [] then 1 else 0 := by
  classical
  unfold aug wordElt
  rw [MonoidAlgebra.lift_single]
  simp only [one_smul]
  change (if FreeMonoid.ofList v = 1 then 1 else 0) = (if v = [] then 1 else 0)
  by_cases hv : v = []
  · subst hv; simp [FreeMonoid.ofList_nil]
  · have h1 : ¬(FreeMonoid.ofList v = 1) := fun h => hv (ofList_eq_one_iff.mp h)
    rw [if_neg h1, if_neg hv]

lemma aug_serreGen (p q : Fin 8) : aug (serreGen p q) = 0 := by
  rw [serreGen, map_sub, map_mul, map_mul, aug_wordElt, aug_wordElt]
  simp

lemma aug_gen (s : FA (Fin 8)) (hs : s ∈ Gen E8) : aug s = 0 := by
  rcases hs with ⟨p, q, hpq, hqp, rfl⟩ | ⟨p, q, hpp, hpq, rfl⟩
  · exact aug_serreGen p q
  · rw [serreGen2, map_sub, map_mul, map_mul, aug_wordElt, aug_serreGen, mul_zero, zero_mul,
      sub_self]

lemma aug_mem_J (x : FA (Fin 8)) (hx : x ∈ J E8) : aug x = 0 := by
  have hle : J E8 ≤ LinearMap.ker aug.toLinearMap := by
    rw [J, Submodule.span_le]
    rintro x ⟨s, hs, u, v, rfl⟩
    change aug (wordElt u * s * wordElt v) = 0
    rw [map_mul, map_mul, aug_gen s hs]
    simp
  exact LinearMap.mem_ker.mp (hle hx)

/-- The highest-weight vector `1 + J` is nonzero. -/
theorem mk_one_ne_zero : (Submodule.Quotient.mk (1 : FA (Fin 8)) : V E8) ≠ 0 := by
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  have := aug_mem_J 1 h
  rw [map_one] at this
  exact one_ne_zero this

instance : Nontrivial (V E8) :=
  ⟨⟨0, Submodule.Quotient.mk (1 : FA (Fin 8)), fun h => mk_one_ne_zero h.symm⟩⟩

/-- `Eᵢ` kills the highest-weight vector. -/
theorem highest_weight_annihilate (lam : Fin 8 → ℂ) (i : Fin 8) :
    Ebar E8 lam i (Submodule.Quotient.mk (1 : FA (Fin 8))) = 0 := by
  rw [Ebar_mk]
  rw [show (1 : FA (Fin 8)) = wordElt [] from wordElt_nil.symm, Eop_apply]
  rfl

/-- `Hᵢ` acts on the highest-weight vector by `lam i`. -/
theorem highest_weight_diagonal (lam : Fin 8 → ℂ) (i : Fin 8) :
    Hbar E8 lam i (Submodule.Quotient.mk (1 : FA (Fin 8)))
      = lam i • Submodule.Quotient.mk (1 : FA (Fin 8)) := by
  rw [Hbar_mk]
  rw [show (1 : FA (Fin 8)) = wordElt [] from wordElt_nil.symm, Hop_apply, Hword]
  rw [show wrho E8 i ([] : List (Fin 8)) = 0 from by simp [wrho]]
  rw [sub_zero, ← Submodule.Quotient.mk_smul]

/-- **Existence of a nonzero module with a highest-weight vector of prescribed weight.** -/
theorem verma_exists (lam : Fin 8 → ℂ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : LieRingModule (LieAlgebra.e₈ ℂ) V)
      (_ : LieModule ℂ (LieAlgebra.e₈ ℂ) V) (v : V),
      v ≠ 0 ∧ (∀ i : Fin 8, ⁅Submission.E8Weights.SerreE i, v⁆ = 0) ∧
      (∀ i : Fin 8, ⁅Submission.E8Weights.SerreH i, v⁆ = lam i • v) := by
  refine ⟨V E8, inferInstance, inferInstance, lieRingModule lam, lieModule lam,
    Submodule.Quotient.mk (1 : FA (Fin 8)), mk_one_ne_zero, ?_, ?_⟩
  · intro i
    show act lam (Submission.E8Weights.SerreE i) (Submodule.Quotient.mk (1 : FA (Fin 8))) = 0
    rw [act_E]
    exact highest_weight_annihilate lam i
  · intro i
    show act lam (Submission.E8Weights.SerreH i) (Submodule.Quotient.mk (1 : FA (Fin 8)))
      = lam i • Submodule.Quotient.mk (1 : FA (Fin 8))
    rw [act_H]
    exact highest_weight_diagonal lam i

open Submission.E8Weights (e h weightInU SerreE SerreH) in
/-- **Non-vanishing of the Verma module** `M(λ) = U(e₈)/J(λ)`: the cyclic highest-weight module
with highest weight `λ` is nontrivial. -/
theorem M_nontrivial (lam : Fin 8 → ℂ) : Nontrivial (Submission.E8Weights.M lam) := by
  let v : V E8 := Submodule.Quotient.mk (1 : FA (Fin 8))
  let ρ : UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ) →ₐ[ℂ] Module.End ℂ (V E8) :=
    UniversalEnvelopingAlgebra.lift ℂ (act lam)
  let ψ : UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ) →ₗ[ℂ] (V E8) :=
    { toFun := fun u => ρ u v
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun c a => by rw [map_smul]; rfl }
  have hψ1 : ψ 1 = v := by
    show ρ 1 v = v
    rw [map_one]; rfl
  have hι : ∀ (x : LieAlgebra.e₈ ℂ), ρ (UniversalEnvelopingAlgebra.ι ℂ x) = act lam x := by
    intro x
    change (UniversalEnvelopingAlgebra.lift ℂ (act lam)) (UniversalEnvelopingAlgebra.ι ℂ x)
      = act lam x
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  have hψmul : ∀ u y : UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ), ψ (u * y) = ρ u (ψ y) := by
    intro u y
    show ρ (u * y) v = ρ u (ρ y v)
    rw [map_mul]; rfl
  have he : ∀ i, ψ (e i) = 0 := by
    intro i
    show ρ (e i) v = 0
    rw [show e i = UniversalEnvelopingAlgebra.ι ℂ (SerreE i) from rfl, hι, act_E, Ebar_mk]
    exact highest_weight_annihilate lam i
  have hh : ∀ j, ψ (h j - weightInU lam j) = 0 := by
    intro j
    show ρ (h j - weightInU lam j) v = 0
    rw [map_sub, LinearMap.sub_apply,
      show h j = UniversalEnvelopingAlgebra.ι ℂ (SerreH j) from rfl, hι, act_H,
      show weightInU lam j = algebraMap ℂ (UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ)) (lam j)
        from rfl, AlgHom.commutes, highest_weight_diagonal]
    rw [show (algebraMap ℂ (Module.End ℂ (V E8)) (lam j))
        = lam j • (1 : Module.End ℂ (V E8)) from rfl, LinearMap.smul_apply]
    rw [show v = Submodule.Quotient.mk (1 : FA (Fin 8)) from rfl]
    simp
  have hJ : ∀ x ∈ Submission.WeightModule.spanIdeal e h (weightInU lam), ψ x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨i, rfl⟩ | ⟨j, rfl⟩
        · exact he i
        · exact hh j
    | zero => simp
    | add y z hy hz ihy ihz => rw [map_add, ihy, ihz, add_zero]
    | smul u y hy ih => rw [show (u • y : UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ)) = u * y
          from rfl, hψmul, ih, map_zero]
  have h1 : ψ (1 : UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ)) ≠ 0 := by
    rw [hψ1]; exact mk_one_ne_zero
  refine ⟨⟨0, Submodule.Quotient.mk (1 : UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ)),
    fun hcon => ?_⟩⟩
  refine h1 (hJ 1 ?_)
  exact (Submodule.Quotient.mk_eq_zero (Submission.WeightModule.spanIdeal e h (weightInU lam))).mp
    hcon.symm

/-! ## Cyclicity of the Verma module -/

/-- The algebra action of `U(e₈)` on `V`, obtained by the universal property from `act`. -/
noncomputable def rho (lam : Fin 8 → ℂ) :
    UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ) →ₐ[ℂ] Module.End ℂ (V E8) :=
  UniversalEnvelopingAlgebra.lift ℂ (act lam)

lemma rho_iota (lam : Fin 8 → ℂ) (x : LieAlgebra.e₈ ℂ) :
    rho lam (UniversalEnvelopingAlgebra.ι ℂ x) = act lam x := by
  change (UniversalEnvelopingAlgebra.lift ℂ (act lam)) (UniversalEnvelopingAlgebra.ι ℂ x)
    = act lam x
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]

lemma rho_F (lam : Fin 8 → ℂ) (i : Fin 8) :
    rho lam (Submission.E8Weights.f i) = Lbar E8 i := by
  rw [show Submission.E8Weights.f i
        = UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF i) from rfl,
    rho_iota, act_F]

lemma rho_H (lam : Fin 8 → ℂ) (i : Fin 8) :
    rho lam (Submission.E8Weights.h i) = Hbar E8 lam i := by
  rw [show Submission.E8Weights.h i
        = UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreH i) from rfl,
    rho_iota, act_H]

open Submission.E8Weights (f) in
lemma rho_fword (lam : Fin 8 → ℂ) (w : List (Fin 8)) :
    rho lam ((w.map f).prod) (Submodule.Quotient.mk (1 : FA (Fin 8)))
      = Submodule.Quotient.mk (wordElt w) := by
  induction w with
  | nil => simp [wordElt_nil]
  | cons i w ih =>
      rw [List.map_cons, List.prod_cons, map_mul]
      change (rho lam (f i)) ((rho lam ((w.map f).prod))
        (Submodule.Quotient.mk (1 : FA (Fin 8)))) = _
      rw [ih, rho_F, Lbar_mk, Lop_wordElt]

lemma rho_cyclic (lam : Fin 8 → ℂ) : ∀ x : FA (Fin 8),
    ∃ u : UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ),
      rho lam u (Submodule.Quotient.mk (1 : FA (Fin 8))) = Submodule.Quotient.mk x := by
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add p q hp hq =>
      obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv⟩ := hq
      exact ⟨u + v, by rw [map_add, LinearMap.add_apply, hu, hv, Submodule.Quotient.mk_add]⟩
  | single w c =>
      refine ⟨c • (((FreeMonoid.toList w).map Submission.E8Weights.f).prod), ?_⟩
      rw [map_smul, LinearMap.smul_apply, rho_fword,
        show MonoidAlgebra.single w c = c • wordElt (FreeMonoid.toList w) by
          rw [wordElt]; simp [MonoidAlgebra.smul_single],
        Submodule.Quotient.mk_smul]

/-- Every element of `V` is `ρ(u) v`, i.e. `V` is a cyclic module generated by the
highest-weight vector `1 + J`. -/
theorem cyclic_V (lam : Fin 8 → ℂ) (z : V E8) :
    ∃ u : UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ),
      rho lam u (Submodule.Quotient.mk (1 : FA (Fin 8))) = z := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (J E8) z
  exact rho_cyclic lam x


end Submission.VermaNonzero
