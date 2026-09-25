import Mathlib
import Submission.Work.CFTLib.ContCohomology.Setup
import Submission.Work.CFTLib.ContCohomology.Inhomogeneous

/-!
# The isomorphism between the complex of invariant continuous functions and the complex of
continuous inhomogeneous cochains

For a topological group `Γ` and the trivial coefficient module `ZMod p`, the complex of
*invariant continuous functions* `homCochain (trivRep p Γ) n` (continuous functions on `Γ^{n+1}`
invariant under the diagonal action) is isomorphic, as a cochain complex, to the complex of
*continuous inhomogeneous cochains* `iCochain p n` (continuous functions on `Γ^n`).

The isomorphism is the classical one coming from the bar resolution: a homogeneous cochain `f` is
sent to the inhomogeneous cochain `g ↦ f (1, g₀, g₀g₁, …, g₀g₁⋯gₙ₋₁)`, i.e. `g ↦ f (partialProd g)`
in terms of Mathlib's prefix products `Fin.partialProd`, while the inverse sends `g` to
`x ↦ g ((x₀)⁻¹x₁, (x₁)⁻¹x₂, …, (xₙ₋₁)⁻¹xₙ)`.
-/

noncomputable section

open TopRep

namespace Work.CFTLib.ContCohomology

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-! ### Elementary facts about the trivial representation and prefix products -/

/-- The representation `trivRep p Γ` acts trivially. -/
@[simp] lemma trivRep_rho_apply (p : ℕ) (g : Γ) (v : ↥(trivRep p Γ)) :
    (trivRep p Γ).ρ g v = v := by
  simp [Work.CFTLib.ContCohomology.trivRep, TopRep.of]

/-- An invariant continuous function (an element of `homCochain (trivRep p Γ) n`) is invariant
under the diagonal left translation of its arguments. -/
lemma homCochain_triv_smul (p n : ℕ) (f : ↥(homCochain (trivRep p Γ) n)) (g : Γ)
    (x : Fin (n + 1) → Γ) : f.1 (g • x) = f.1 x := by
  have h := f.2.2 g x
  rw [show (g • x) = (fun i => g * x i) from funext fun i => rfl, h]
  simp [Work.CFTLib.ContCohomology.trivRep, TopRep.of]

/-- The `i`-th prefix product `x ↦ (x₀, …, x_{i-1})` is continuous. -/
lemma continuous_partialProd (n : ℕ) (i : Fin (n + 1)) :
    Continuous fun x : Fin n → Γ => Fin.partialProd x i := by
  induction i using Fin.induction with
  | zero => simp only [Fin.partialProd_zero]; exact continuous_const
  | succ j ih => simp only [Fin.partialProd_succ]; exact ih.mul (continuous_apply j)

/-- The map sending a tuple to its tuple of prefix products is continuous. -/
lemma continuous_partialProd' (n : ℕ) :
    Continuous fun x : Fin n → Γ => Fin.partialProd x :=
  continuous_pi fun i => continuous_partialProd n i

/-! ### The two directions of the isomorphism -/

variable (p : ℕ)

/-- **Homogeneous cochains to inhomogeneous cochains**: `f ↦ (g ↦ f (1, g₀, g₀g₁, …))`. -/
def homToInh (n : ℕ) :
    ↥(homCochain (trivRep p Γ) n) →ₗ[ZMod p] ↥(iCochain (Γ := Γ) p n) where
  toFun f := ⟨fun y => f.1 (Fin.partialProd y), f.2.1.comp (continuous_partialProd' n)⟩
  map_add' f g := by
    apply Subtype.ext; funext y; simp
  map_smul' r f := by
    apply Subtype.ext; funext y; simp

/-- **Inhomogeneous cochains to homogeneous cochains**: `g ↦ (x ↦ g (x₀⁻¹x₁, x₁⁻¹x₂, …))`. -/
def inhToHom (n : ℕ) :
    ↥(iCochain (Γ := Γ) p n) →ₗ[ZMod p] ↥(homCochain (trivRep p Γ) n) where
  toFun g := ⟨fun x => g.1 (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ), by
    refine ⟨g.2.comp (continuous_pi fun i => ?_), ?_⟩
    · exact ((continuous_apply i.castSucc).inv).mul (continuous_apply i.succ)
    · intro g₀ x
      have hfun : (fun i : Fin n =>
            ((fun k => g₀ * x k) i.castSucc)⁻¹ * (fun k => g₀ * x k) i.succ)
          = (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) := by
        funext i
        simp only [mul_inv_rev]
        group
      show g.1 (fun i : Fin n => ((fun k => g₀ * x k) i.castSucc)⁻¹ *
          (fun k => g₀ * x k) i.succ)
        = (trivRep p Γ).ρ g₀ (g.1 (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ))
      rw [hfun, trivRep_rho_apply]⟩
  map_add' g h := by
    apply Subtype.ext; funext x; simp
  map_smul' r g := by
    apply Subtype.ext; funext x; simp

@[simp] lemma homToInh_apply (n : ℕ) (f : ↥(homCochain (trivRep p Γ) n)) (y : Fin n → Γ) :
    (homToInh p n f).1 y = f.1 (Fin.partialProd y) := rfl

@[simp] lemma inhToHom_apply (n : ℕ) (g : ↥(iCochain (Γ := Γ) p n)) (x : Fin (n + 1) → Γ) :
    (inhToHom p n g).1 x
      = g.1 (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) := rfl

/-- The two directions are inverse to each other. -/
lemma inhToHom_homToInh (n : ℕ) (f : ↥(homCochain (trivRep p Γ) n)) :
    inhToHom p n (homToInh p n f) = f := by
  apply Subtype.ext
  funext x
  rw [inhToHom_apply, homToInh_apply]
  have h' : Fin.partialProd (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ)
      = (x 0)⁻¹ • x := by
    funext i
    have hh := congrFun (Fin.partialProd_left_inv x) i
    simp only [Pi.smul_apply, smul_eq_mul] at hh ⊢
    rw [← hh, inv_mul_cancel_left]
  rw [h', homCochain_triv_smul]

/-- The other composition is the identity as well. -/
lemma homToInh_inhToHom (n : ℕ) (g : ↥(iCochain (Γ := Γ) p n)) :
    homToInh p n (inhToHom p n g) = g := by
  apply Subtype.ext
  funext y
  rw [homToInh_apply, inhToHom_apply]
  have h' : (fun i : Fin n => (Fin.partialProd y i.castSucc)⁻¹ * Fin.partialProd y i.succ) = y := by
    funext i
    exact Fin.partialProd_right_inv y i
  rw [h']

/-- **The isomorphism between the modules of homogeneous and inhomogeneous continuous cochains**
in degree `n`, given by the classical formula of the bar resolution. -/
def homIsoInh (n : ℕ) :
    ↥(homCochain (trivRep p Γ) n) ≃ₗ[ZMod p] ↥(iCochain (Γ := Γ) p n) :=
  LinearEquiv.ofLinearMap (homToInh p n) (inhToHom p n)
    (LinearMap.ext fun g => homToInh_inhToHom p n g)
    (LinearMap.ext fun f => inhToHom_homToInh p n f)

@[simp] lemma homIsoInh_apply (n : ℕ) (f : ↥(homCochain (trivRep p Γ) n)) :
    homIsoInh p n f = homToInh p n f := rfl

/-! ### Compatibility with the differentials -/

/-- **The isomorphism is a map of complexes**: it intertwines the homogeneous differential
`homDiff` with the inhomogeneous differential `iDiff`. -/
theorem homIsoInh_homDiff (n : ℕ) (f : ↥(homCochain (trivRep p Γ) n)) :
    homIsoInh p (n + 1) (homDiff (trivRep p Γ) n f)
      = iDiff (Γ := Γ) p n (homIsoInh p n f) := by
  rw [homIsoInh_apply, homIsoInh_apply]
  apply Subtype.ext
  funext y
  show (homDiff (trivRep p Γ) n f).1 (Fin.partialProd y)
      = (iDiff (Γ := Γ) p n (homToInh p n f)).1 y
  rw [homDiff_apply, iDiff_apply]
  simp only [deleteMap, ContinuousMap.coe_mk, homToInh_apply]
  have hzero : (-1 : ZMod p) ^ (((0 : Fin (n + 2)) : ℕ)) •
        f.1 (Fin.partialProd y ∘ Fin.succAbove (0 : Fin (n + 2)))
      = f.1 (Fin.partialProd (Fin.tail y)) := by
    rw [show (((0 : Fin (n + 2)) : ℕ)) = 0 from rfl, pow_zero, one_smul]
    have hfun : (Fin.partialProd y ∘ Fin.succAbove (0 : Fin (n + 2)))
        = y 0 • Fin.partialProd (Fin.tail y) := by
      funext j
      rw [Function.comp_apply, Fin.succAbove_zero_apply, Pi.smul_apply, smul_eq_mul,
        Fin.partialProd_succ']
    rw [hfun, homCochain_triv_smul]
  have hterm : ∀ j : Fin (n + 1),
      (-1 : ZMod p) ^ (((j.succ : Fin (n + 2)) : ℕ)) •
          f.1 (Fin.partialProd y ∘ Fin.succAbove (j.succ : Fin (n + 2)))
        = (-1 : ZMod p) ^ ((j : ℕ) + 1) •
          f.1 (Fin.partialProd (Fin.contractNth j (· * ·) y)) := by
    intro j
    rw [← Fin.partialProd_contractNth y j, Fin.val_succ]
  rw [Fin.sum_univ_succ, hzero]
  congr 1
  exact Finset.sum_congr rfl fun j _ => hterm j

/-- The complex of invariant continuous functions (`homCochain`) is isomorphic to the complex of
continuous inhomogeneous cochains (`iCochain`): the isomorphism is the classical one sending a
homogeneous cochain `f` to `g ↦ f (1, g₀, g₀g₁, …, g₀g₁⋯gₙ₋₁)`. -/
theorem exists_homCochain_iso_iCochain
    (p : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    ∃ e : (n : ℕ) → ↥(Work.CFTLib.ContCohomology.homCochain
          (Work.CFTLib.ContCohomology.trivRep p Γ) n) ≃ₗ[ZMod p]
        ↥(Work.CFTLib.ContCohomology.iCochain (Γ := Γ) p n),
      ∀ (n : ℕ) (f : ↥(Work.CFTLib.ContCohomology.homCochain
          (Work.CFTLib.ContCohomology.trivRep p Γ) n)),
        e (n+1) (Work.CFTLib.ContCohomology.homDiff
          (Work.CFTLib.ContCohomology.trivRep p Γ) n f) =
          Work.CFTLib.ContCohomology.iDiff (Γ := Γ) p n (e n f) :=
  ⟨fun n => homIsoInh p n, fun n f => homIsoInh_homDiff p n f⟩

end Work.CFTLib.ContCohomology
