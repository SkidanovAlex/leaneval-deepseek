import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.annAtDefs
import Submission.Work.ORLyndon.FoxComp
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero
import Submission.Work.OROneRel.presentedGroup_map_injective_of_preimage

/-!
# Nielsen invariance of the annihilator of the root Fox vector

`Work.ORLyndon.annAt K (u ^ l) u E` says that the componentwise annihilator of the Fox vector
`(∂u/∂x)_x` of the root `u` is trivial in `K[⟨X | u ^ l⟩]`.  This file proves that the statement at
the **full letter set** (equivalently: the triviality `Vann K (u ^ l) u` of the annihilator of the
whole vector) is **invariant under automorphisms of the free group** (in particular under Nielsen
transformations): for a bijective `ψ : FreeGroup X →* FreeGroup X`,

`Vann K ((ψ u) ^ l) (ψ u)  →  Vann K (u ^ l) u`.

The proof is the Fox chain rule `Work.ORLyndon.foxD_comp`: the Fox vector of `ψ u` is the image of
the Fox vector of `u` under the ring map induced by `ψ` on the group algebras, contracted with the
Jacobian `(∂(ψ x)/∂y)_{x,y}`.  Consequently, if `b` annihilates the vector of `u`, then the image of
`b` under the induced map of group algebras annihilates the vector of `ψ u`, and the conclusion
follows from the injectivity of that map (the induced map of one-relator groups is the isomorphism
`⟨X | u ^ l⟩ ≅ ⟨X | (ψ u) ^ l⟩`).

## Consequence

Any sufficient condition for `Vann` (the level criterion `Work.ORLyndon.annAt_of_occTerm_dominated`,
the single-occurrence criterion `isUnit_rootVec_of_letterOnce`, the two-occurrence criterion
`annAt_of_twoOcc`, the Magnus-subgroup criterion `annAt_of_support_le_magnusSubgroup`, ...) may be
applied to **any automorphic image of the root**, which is a strict enlargement of the reach of each
of them; see `Work.ORLyndon.epsNeZeroDescent_of_vann_aut` in `epsNeZeroDescent.lean`.

## Main results

* `Work.ORLyndon.Vann` -- the triviality of the annihilator of the root Fox *vector*;
* `Work.ORLyndon.vann_iff_annAt_letters` -- `Vann ⟺ annAt` at the set of letters of the root;
* `Work.ORLyndon.psiBar`, `Work.ORLyndon.psiBar_mk`, `Work.ORLyndon.psiBar_injective` -- the induced
  map of one-relator groups and its injectivity;
* `Work.ORLyndon.mapDomainRingHom_psiBar_rootVec` -- the chain-rule compatibility;
* `Work.ORLyndon.vann_of_vann_psi` -- the transfer.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

variable {X : Type u} [DecidableEq X] {K : Type v} [Field K]

/-- **The annihilator of the root Fox *vector* is trivial.**  No non-zero element of `K[⟨X | r⟩]`
kills every component of `(∂u/∂x)_x` at once. -/
def Vann (K : Type v) [Field K] {X : Type u} [DecidableEq X] (r u : FreeGroup X) : Prop :=
  ∀ b : MonoidAlgebra K (OneRelatorGroup r), b • rootVec K r u = 0 → b = 0

/-- The `x`-component of the root Fox vector vanishes when `x` is not a letter of the root. -/
theorem rootVec_eq_zero_of_notMem_letters {r u : FreeGroup X} {x : X}
    (hx : x ∉ Work.OROneRel.relatorLetters u) : rootVec K r u x = 0 := by
  rw [rootVec_apply, foxD_eq_zero_of_notMem_relatorLetters x u hx, map_zero]

/-- `Vann` implies `annAt` at the set of letters of the root: off the letters the components
vanish. -/
theorem annAt_letters_of_vann {r u : FreeGroup X} (h : Vann K r u) :
    annAt K r u (Work.OROneRel.relatorLetters u) := by
  intro b hb
  refine h b (Finsupp.ext fun x => ?_)
  rw [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul]
  by_cases hx : x ∈ Work.OROneRel.relatorLetters u
  · exact hb x hx
  · rw [rootVec_eq_zero_of_notMem_letters (K := K) hx, mul_zero]

/-- Conversely, `annAt` at the set of letters of the root implies `Vann`. -/
theorem vann_of_annAt_letters {r u : FreeGroup X}
    (h : annAt K r u (Work.OROneRel.relatorLetters u)) : Vann K r u := by
  intro b hb
  refine h b fun x hx => ?_
  have h1 := congrArg (fun v : X →₀ MonoidAlgebra K (OneRelatorGroup r) => v x) hb
  simpa only [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul] using h1

/-- `Vann` and `annAt` at the letter set of the root are the same statement. -/
theorem vann_iff_annAt_letters {r u : FreeGroup X} :
    Vann K r u ↔ annAt K r u (Work.OROneRel.relatorLetters u) :=
  ⟨annAt_letters_of_vann, vann_of_annAt_letters⟩

/-! ## The induced map of one-relator groups -/

/-- **The map of one-relator groups induced by an endomorphism `ψ` of the free group**: it exists
because `ψ (u ^ l) = (ψ u) ^ l`. -/
noncomputable def psiBar (ψ : FreeGroup X →* FreeGroup X) (u : FreeGroup X) (l : ℕ) :
    OneRelatorGroup (u ^ l) →* OneRelatorGroup ((ψ u) ^ l) :=
  PresentedGroup.map ψ (by
    intro x hx
    rw [Set.mem_singleton_iff] at hx ⊢
    subst hx
    rw [map_pow])

/-- `psiBar` on the class of a word is the class of the image. -/
theorem psiBar_mk (ψ : FreeGroup X →* FreeGroup X) (u : FreeGroup X) (l : ℕ)
    (x : FreeGroup X) :
    psiBar ψ u l (PresentedGroup.mk ({u ^ l} : Set (FreeGroup X)) x) =
      PresentedGroup.mk ({((ψ u) ^ l)} : Set (FreeGroup X)) (ψ x) :=
  rfl

/-- `psiBar` is the map induced on the classes. -/
theorem psiBar_presentRho (ψ : FreeGroup X →* FreeGroup X) (u : FreeGroup X) (l : ℕ) :
    (psiBar ψ u l).comp (presentRho (u ^ l)) = (presentRho ((ψ u) ^ l)).comp ψ := by
  refine MonoidHom.ext fun x => ?_
  change psiBar ψ u l (PresentedGroup.mk _ x) = PresentedGroup.mk _ (ψ x)
  exact psiBar_mk ψ u l x

/-- **The normal closure of a surjective image is the image of the normal closure.** -/
theorem map_normalClosure_of_surjective (ψ : FreeGroup X →* FreeGroup X)
    (hσ : Function.Surjective ψ) (w : FreeGroup X) :
    (Subgroup.normalClosure ({w} : Set (FreeGroup X))).map ψ =
      Subgroup.normalClosure ({ψ w} : Set (FreeGroup X)) := by
  rw [Subgroup.map_normalClosure _ ψ hσ, Set.image_singleton]

/-- **The normal closure of an automorphic image is the image of the normal closure.** -/
theorem map_normalClosure_of_mulEquiv (ψ : FreeGroup X ≃* FreeGroup X) (w : FreeGroup X) :
    (Subgroup.normalClosure ({w} : Set (FreeGroup X))).map ψ.toMonoidHom =
      Subgroup.normalClosure ({ψ w} : Set (FreeGroup X)) := by
  rw [Subgroup.map_normalClosure _ ψ.toMonoidHom ψ.surjective, Set.image_singleton]
  simp only [MulEquiv.coe_toMonoidHom]

/-- The preimage condition of `Work.OROneRel.presentedGroup_map_injective_of_preimage` for a
bijective endomorphism. -/
theorem preimage_normalClosure_iff (ψ : FreeGroup X →* FreeGroup X) (hι : Function.Injective ψ)
    (hσ : Function.Surjective ψ) (u : FreeGroup X) (l : ℕ) (x : FreeGroup X) :
    ψ x ∈ Subgroup.normalClosure ({((ψ u) ^ l)} : Set (FreeGroup X)) ↔
      x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)) := by
  have hmap : (Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X))).map ψ =
      Subgroup.normalClosure ({((ψ u) ^ l)} : Set (FreeGroup X)) := by
    rw [map_normalClosure_of_surjective ψ hσ (u ^ l), map_pow]
  rw [← hmap, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [hι hyx] at hy
  · exact fun hx => ⟨x, hx, rfl⟩

/-- **`psiBar` is injective for a bijective `ψ`.** -/
theorem psiBar_injective (ψ : FreeGroup X →* FreeGroup X) (hι : Function.Injective ψ)
    (hσ : Function.Surjective ψ) (u : FreeGroup X) (l : ℕ) :
    Function.Injective (psiBar ψ u l) := by
  obtain ⟨Φ, hinj, hΦ⟩ :=
    Work.OROneRel.presentedGroup_map_injective_of_preimage (ρ := ψ) (v := u) (u := ψ u) l
      (preimage_normalClosure_iff ψ hι hσ u l)
  have hEq : Φ = psiBar ψ u l := by
    refine MonoidHom.ext fun a => ?_
    obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective _ a
    rw [hΦ x, psiBar_mk]
  rwa [hEq] at hinj

/-! ## The chain-rule compatibility -/

/-- **The chain-rule compatibility**, in the direction used below: the image under `psiBar` of
`presentAlg a` is `presentAlg` of the image of `a` under `ψ`. -/
theorem mapDomainRingHom_psiBar_presentAlg (ψ : FreeGroup X →* FreeGroup X) (u : FreeGroup X)
    (l : ℕ) (a : MonoidAlgebra K (FreeGroup X)) :
    MonoidAlgebra.mapDomainRingHom K (psiBar ψ u l) (presentAlg K (u ^ l) a) =
      presentAlg K ((ψ u) ^ l) (MonoidAlgebra.mapDomainRingHom K ψ a) := by
  have hcomp : (psiBar ψ u l).comp (presentRho (u ^ l)) =
      (presentRho ((ψ u) ^ l)).comp ψ := psiBar_presentRho ψ u l
  simp only [presentAlg]
  rw [← RingHom.comp_apply, ← MonoidAlgebra.mapDomainRingHom_comp, hcomp,
    MonoidAlgebra.mapDomainRingHom_comp, RingHom.comp_apply]

/-- The chain-rule compatibility, in the shape in which the transfer uses it. -/
theorem mapDomainRingHom_psiBar_rootVec (ψ : FreeGroup X →* FreeGroup X) (u : FreeGroup X)
    (l : ℕ) (q : X) :
    MonoidAlgebra.mapDomainRingHom K (psiBar ψ u l) (rootVec K (u ^ l) u q) =
      presentAlg K ((ψ u) ^ l) (MonoidAlgebra.mapDomainRingHom K ψ (foxD (K := K) q u)) := by
  rw [rootVec_apply]
  exact mapDomainRingHom_psiBar_presentAlg ψ u l (foxD (K := K) q u)

/-! ## The transfer -/

/-- **Invariance of `Vann` under bijective endomorphisms of the free group** (in particular under
Nielsen transformations).  The triviality of the annihilator of the root Fox vector of `ψ u` implies
the same for `u`. -/
theorem vann_of_vann_psi (ψ : FreeGroup X →* FreeGroup X) (hι : Function.Injective ψ)
    (hσ : Function.Surjective ψ) (u : FreeGroup X) (l : ℕ)
    (h : Vann K ((ψ u) ^ l) (ψ u)) : Vann K (u ^ l) u := by
  intro b hb
  have hbq : ∀ q : X, b * rootVec K (u ^ l) u q = 0 := by
    intro q
    have h1 := congrArg (fun v : X →₀ MonoidAlgebra K (OneRelatorGroup (u ^ l)) => v q) hb
    simpa only [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul] using h1
  have hB : MonoidAlgebra.mapDomainRingHom K (psiBar ψ u l) b
      • rootVec K ((ψ u) ^ l) (ψ u) = 0 := by
    apply Finsupp.ext
    intro y
    rw [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul, rootVec_apply,
      foxD_comp ψ y u, Finsupp.sum, map_sum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [foxFD_apply, map_mul, ← mapDomainRingHom_psiBar_rootVec ψ u l q,
      ← mul_assoc, ← map_mul, hbq q, map_zero, zero_mul]
  have h0 : MonoidAlgebra.mapDomainRingHom K (psiBar ψ u l) b = 0 := h _ hB
  exact MonoidAlgebra.mapDomain_injective (psiBar_injective ψ hι hσ u l)
    (by rw [MonoidAlgebra.mapDomain_zero]
        simpa only [MonoidAlgebra.mapDomainRingHom_apply] using h0)

end Work.ORLyndon
