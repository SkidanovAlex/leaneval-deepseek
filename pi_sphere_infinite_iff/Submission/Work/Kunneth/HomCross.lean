import Mathlib
import Submission.Work.Kunneth.CrossShuffle
import Submission.Work.Kunneth.EZMap
import Submission.Work.Kunneth.ezHom_d
import Submission.Work.Kunneth.Splitting
import Submission.Work.Kunneth.kronecker_ezChain
import Submission.Work.Cohomology.relCapHHom

/-!
# The homology cross product

For simplicial sets `X`, `Y` whose homology is free (projective) in each degree, and degrees
`p`, `q`, the **homology cross product**

  `Work.Kunneth.homCrossLin X Y p q hX hY : H_p(X;ℤ) ⊗ H_q(Y;ℤ) → H_{p+q}(X × Y;ℤ)`

sends `x ⊗ y` to the homology class of the Eilenberg–Zilber shuffle chain `ezChain p q X Y u v`
of cycle representatives of `x` and `y`; by `Work.Kunneth.ezMap_tpLof` this chain is
`ezMap (tpLof (u ⊗ v))`, so the construction is the one forced by the shuffle map.

The representatives are produced by `Work.Kunneth.homSec`, a *linear* section of the cycle-class
map `homologyπ : Z_n → H_n` of a complex with projective homology; choosing the section linearly
(rather than by `Classical.choose` on each class) is what makes the cross product bilinear.

## Main results

* `homSec`, `homSec_spec` — the linear section of `homologyπ`;
* `ezMap_tpLof` — the shuffle map on a summand generator is `ezChain`;
* `homCrossChain`, `d_homCrossChain` — the shuffle chain of two cycles is a cycle;
* `homCrossCycTens`, `homCrossLin` — the cross product of cycles and of homology classes;
* `homCrossLin_tmul`, `iCycles_homCrossLin_tmul` — its computation rules;
* `kronH_homCrossLin` — the Kronecker rule `⟨α × β, x × y⟩ = ⟨α,x⟩·⟨β,y⟩`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule
attribute [local instance 5000] Submodule.module

/-! ## A linear section of the cycle-class map -/

/-- **A linear section of `homologyπ : Z_n → H_n`**, for a chain complex with projective homology
in degree `n`: a linear map picking a cycle in each homology class. -/
noncomputable def homSec (D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (hH : Module.Projective ℤ ↥(D.homology n)) : ↥(D.homology n) →ₗ[ℤ] ↥(D.cycles n) :=
  Classical.choose (Module.projective_lifting_property (D.homologyπ n).hom LinearMap.id
    ((ModuleCat.epi_iff_surjective (D.homologyπ n)).mp inferInstance))

/-- The defining property of the section: the class of `homSec y` is `y`. -/
theorem homSec_spec (D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (hH : Module.Projective ℤ ↥(D.homology n)) (y : ↥(D.homology n)) :
    (D.homologyπ n).hom (homSec D n hH y) = y := by
  have h : (D.homologyπ n).hom ∘ₗ homSec D n hH = LinearMap.id := by
    simpa only [homSec] using Classical.choose_spec
      (Module.projective_lifting_property (D.homologyπ n).hom LinearMap.id
        ((ModuleCat.epi_iff_surjective (D.homologyπ n)).mp inferInstance))
  exact LinearMap.congr_fun h y

/-- The inclusion of the cycles is killed by the differential. -/
theorem d_iCycles (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (z : ↥(K.cycles n)) :
    (K.d n (n - 1)).hom ((K.iCycles n).hom z) = 0 := by
  have h := congrArg (fun (g : K.cycles n ⟶ K.X (n - 1)) => g.hom z)
    (HomologicalComplex.iCycles_d K n (n - 1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

end

end Work.Kunneth

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule
attribute [local instance 5000] Submodule.module

/-! ## Linearity of `cycleOfChain` in its chain argument -/

/-- `cycleOfChain` is insensitive to the proof argument. -/
theorem cycleOfChain_proof_irrel (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (x : ↥(K.X n))
    (h h' : (K.d n (n - 1)).hom x = 0) :
    cycleOfChain K n x h = cycleOfChain K n x h' := by
  apply Work.Cohomology.iCycles_injective_C ℤ K n
  rw [iCycles_cycleOfChain]

/-! ## The shuffle chain of two chains -/

/-- The Eilenberg–Zilber shuffle map on a pure tensor: `ezMap (tpLof (u ⊗ v)) = ezChain u v`. -/
theorem ezMap_tpLof (X Y : SSet) (p q : ℕ)
    (u : ↥((sChain X).X p)) (v : ↥((sChain Y).X q)) :
    ((ezMap X Y).f (p + q)).hom
        (tpLof (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩ (u ⊗ₜ[ℤ] v))
      = Work.KunnethEZ.ezChain p q X Y u v := by
  rw [ezMap_f, ezHom_apply_tpLof X Y p q (p + q) rfl, ezSummandLin_tmul_chain]
  simp

/-- The `(p,q)`-summand component of the Eilenberg–Zilber shuffle map, with the total degree `n`
given explicitly (`h : p + q = n`). -/
noncomputable def homCrossChain (X Y : SSet) (n p q : ℕ) (h : p + q = n) :
    ↥((sChain X).X p ⊗ (sChain Y).X q) →ₗ[ℤ] ↥((sChain (sProd X Y)).X n) :=
  ((ezMap X Y).f n).hom.comp (tpLof (sChain X) (sChain Y) n ⟨(p, q), h⟩)

/-- The computation rule for `homCrossChain`. -/
theorem homCrossChain_tmul (X Y : SSet) (n p q : ℕ) (h : p + q = n)
    (u : ↥((sChain X).X p)) (v : ↥((sChain Y).X q)) :
    homCrossChain X Y n p q h (u ⊗ₜ[ℤ] v)
      = ((ezMap X Y).f n).hom
          (tpLof (sChain X) (sChain Y) n ⟨(p, q), h⟩ (u ⊗ₜ[ℤ] v)) := rfl

/-- **The shuffle chain of two cycles is a cycle.** -/
theorem d_homCrossChain (X Y : SSet) (n p q : ℕ) (h : p + q = n)
    (u : ↥((sChain X).X p)) (v : ↥((sChain Y).X q))
    (hu : ((sChain X).d p (p - 1)).hom u = 0) (hv : ((sChain Y).d q (q - 1)).hom v = 0) :
    ((sChain (sProd X Y)).d n (n - 1)).hom (homCrossChain X Y n p q h (u ⊗ₜ[ℤ] v)) = 0 := by
  rw [homCrossChain_tmul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [show ((sChain (sProd X Y)).d (0 : ℕ) (0 - 1)) = 0 from
      (sChain (sProd X Y)).shape 0 0 (by simp [ComplexShape.down]), ModuleCat.hom_zero,
      LinearMap.zero_apply]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hcomm : ((sChain (sProd X Y)).d (m + 1) m).hom
          (((ezMap X Y).f (m + 1)).hom
            ((tpLof (sChain X) (sChain Y) (m + 1) ⟨(p, q), h⟩) (u ⊗ₜ[ℤ] v)))
        = ((ezMap X Y).f m).hom
          ((ModuleCat.Hom.hom ((tChain X Y).d (m + 1) m))
            ((tpLof (sChain X) (sChain Y) (m + 1) ⟨(p, q), h⟩) (u ⊗ₜ[ℤ] v))) := by
      have hc := congrArg (fun (g : (tChain X Y).X (m + 1) ⟶ (sChain (sProd X Y)).X m) =>
          (ModuleCat.Hom.hom g)
            ((tpLof (sChain X) (sChain Y) (m + 1) ⟨(p, q), h⟩) (u ⊗ₜ[ℤ] v)))
        ((ezMap X Y).comm' (m + 1) m (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl))
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hc
    show ((sChain (sProd X Y)).d (m + 1) m).hom
        (((ezMap X Y).f (m + 1)).hom
          ((tpLof (sChain X) (sChain Y) (m + 1) ⟨(p, q), h⟩) (u ⊗ₜ[ℤ] v))) = 0
    rw [hcomm, tpC_d]
    simp only [ModuleCat.hom_ofHom]
    have h0 : tpD (sChain X) (sChain Y) m
        ((tpLof (sChain X) (sChain Y) (m + 1) ⟨(p, q), h⟩) (u ⊗ₜ[ℤ] v)) = 0 := by
      rw [tpD_lof_tmul]
      split_ifs <;> simp only [hu, hv, TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero,
        add_zero, zero_add]
      all_goals exact smul_zero ((-1 : ℤ) ^ p)
    erw [h0, map_zero]

/-! ## The cross product of cycles -/

/-- The underlying map of the cross product of cycles: the shuffle map on the tensor product of
the cycle modules. -/
noncomputable def homCrossCycMap (X Y : SSet) (p q : ℕ) :
    ↥((sChain X).cycles p ⊗ (sChain Y).cycles q) →ₗ[ℤ]
      ↥((sChain (sProd X Y)).X (p + q)) :=
  (homCrossChain X Y (p + q) p q rfl).comp
    (TensorProduct.map (((sChain X).iCycles p).hom) (((sChain Y).iCycles q).hom))

theorem homCrossCycMap_tmul (X Y : SSet) (p q : ℕ)
    (z : ↥((sChain X).cycles p)) (w : ↥((sChain Y).cycles q)) :
    homCrossCycMap X Y p q (z ⊗ₜ[ℤ] w)
      = homCrossChain X Y (p + q) p q rfl
          (((sChain X).iCycles p).hom z ⊗ₜ[ℤ] ((sChain Y).iCycles q).hom w) := by
  rw [homCrossCycMap, LinearMap.comp_apply]
  erw [TensorProduct.map_tmul]

/-- The cross product of cycles is a cycle. -/
theorem d_homCrossCycMap (X Y : SSet) (p q : ℕ)
    (x : ↥((sChain X).cycles p ⊗ (sChain Y).cycles q)) :
    ((sChain (sProd X Y)).d (p + q) (p + q - 1)).hom (homCrossCycMap X Y p q x) = 0 := by
  refine TensorProduct.induction_on (motive := fun x =>
    ((sChain (sProd X Y)).d (p + q) (p + q - 1)).hom (homCrossCycMap X Y p q x) = 0) x ?_ ?_ ?_
  · simp
  · intro z w
    rw [homCrossCycMap_tmul]
    exact d_homCrossChain X Y (p + q) p q rfl _ _ (d_iCycles (sChain X) p z)
      (d_iCycles (sChain Y) q w)
  · intro a b ha hb
    rw [map_add, map_add, ha, hb, add_zero]

/-- The cross product of cycles is a chain map into the cycles of the product (the `hk` input of
`liftCycles`). -/
theorem homCrossCycMap_d (X Y : SSet) (p q : ℕ) :
    ModuleCat.ofHom (homCrossCycMap X Y p q) ≫ (sChain (sProd X Y)).d (p + q) (p + q - 1)
      = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    ModuleCat.hom_zero, LinearMap.zero_apply] using d_homCrossCycMap X Y p q x

/-- **The cross product of two cycles**, as a cycle of the product.  It is the lift of the
Eilenberg–Zilber shuffle chain through the cycles of `X × Y`. -/
noncomputable def homCrossCycTens (X Y : SSet) (p q : ℕ) :
    ↥((sChain X).cycles p ⊗ (sChain Y).cycles q) →ₗ[ℤ]
      ↥((sChain (sProd X Y)).cycles (p + q)) :=
  ModuleCat.Hom.hom ((sChain (sProd X Y)).liftCycles
    (ModuleCat.ofHom (homCrossCycMap X Y p q)) (p + q - 1) (downNext (p + q))
    (homCrossCycMap_d X Y p q))

/-- The value of `liftCycles` on an element of a general source module. -/
theorem iCycles_liftCycles_apply_gen (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) {A : ModuleCat ℤ}
    (k : A ⟶ K.X n) (hj : (ComplexShape.down ℕ).next n = n - 1)
    (hk : k ≫ K.d n (n - 1) = 0) (a : ↥A) :
    (K.iCycles n).hom ((K.liftCycles k (n - 1) hj hk).hom a) = (ModuleCat.Hom.hom k) a := by
  have h := congrArg (fun (g : A ⟶ K.X n) => (ModuleCat.Hom.hom g) a)
    (HomologicalComplex.liftCycles_i K k (n - 1) hj hk)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The underlying chain of the cross product of two cycles is the shuffle chain. -/
theorem iCycles_homCrossCycTens (X Y : SSet) (p q : ℕ)
    (x : ↥((sChain X).cycles p ⊗ (sChain Y).cycles q)) :
    ((sChain (sProd X Y)).iCycles (p + q)).hom (homCrossCycTens X Y p q x)
      = homCrossCycMap X Y p q x := by
  have h := iCycles_liftCycles_apply_gen (sChain (sProd X Y)) (p + q)
    (ModuleCat.ofHom (homCrossCycMap X Y p q)) (downNext (p + q)) (homCrossCycMap_d X Y p q) x
  simpa only [homCrossCycTens, ModuleCat.hom_ofHom] using h

/-- The cross product of two cycles, on pure tensors. -/
theorem iCycles_homCrossCycTens_tmul (X Y : SSet) (p q : ℕ)
    (z : ↥((sChain X).cycles p)) (w : ↥((sChain Y).cycles q)) :
    ((sChain (sProd X Y)).iCycles (p + q)).hom (homCrossCycTens X Y p q (z ⊗ₜ[ℤ] w))
      = Work.KunnethEZ.ezChain p q X Y (((sChain X).iCycles p).hom z)
          (((sChain Y).iCycles q).hom w) := by
  rw [iCycles_homCrossCycTens, homCrossCycMap_tmul, homCrossChain_tmul, ezMap_tpLof]

/-! ## The homology cross product -/

/-- **The homology cross product** `H_p(X;ℤ) ⊗ H_q(Y;ℤ) → H_{p+q}(X × Y;ℤ)`. -/
noncomputable def homCrossLin (X Y : SSet) (p q : ℕ)
    (hX : ∀ n, Module.Projective ℤ ↥((sChain X).homology n))
    (hY : ∀ n, Module.Projective ℤ ↥((sChain Y).homology n)) :
    ↥((sChain X).homology p ⊗ (sChain Y).homology q) →ₗ[ℤ]
      ↥((sChain (sProd X Y)).homology (p + q)) :=
  ((sChain (sProd X Y)).homologyπ (p + q)).hom.comp
    ((homCrossCycTens X Y p q).comp (TensorProduct.map (homSec (sChain X) p (hX p))
      (homSec (sChain Y) q (hY q))))

/-- The computation rule for the homology cross product. -/
theorem homCrossLin_tmul (X Y : SSet) (p q : ℕ)
    (hX : ∀ n, Module.Projective ℤ ↥((sChain X).homology n))
    (hY : ∀ n, Module.Projective ℤ ↥((sChain Y).homology n))
    (x : ↥((sChain X).homology p)) (y : ↥((sChain Y).homology q)) :
    homCrossLin X Y p q hX hY (x ⊗ₜ[ℤ] y)
      = ((sChain (sProd X Y)).homologyπ (p + q)).hom
          (homCrossCycTens X Y p q
            (homSec (sChain X) p (hX p) x ⊗ₜ[ℤ] homSec (sChain Y) q (hY q) y)) := by
  rw [homCrossLin, LinearMap.comp_apply, LinearMap.comp_apply]
  erw [TensorProduct.map_tmul]

/-- The underlying chain of the homology cross product of two classes: it is the Eilenberg–Zilber
shuffle chain of the chosen cycle representatives. -/
theorem iCycles_homCrossLin_tmul (X Y : SSet) (p q : ℕ)
    (hX : ∀ n, Module.Projective ℤ ↥((sChain X).homology n))
    (hY : ∀ n, Module.Projective ℤ ↥((sChain Y).homology n))
    (x : ↥((sChain X).homology p)) (y : ↥((sChain Y).homology q)) :
    ((sChain (sProd X Y)).iCycles (p + q)).hom
        (homCrossCycTens X Y p q
          (homSec (sChain X) p (hX p) x ⊗ₜ[ℤ] homSec (sChain Y) q (hY q) y))
      = Work.KunnethEZ.ezChain p q X Y
          (((sChain X).iCycles p).hom (homSec (sChain X) p (hX p) x))
          (((sChain Y).iCycles q).hom (homSec (sChain Y) q (hY q) y)) :=
  iCycles_homCrossCycTens_tmul X Y p q _ _

/-- **The Kronecker rule for the cross products**: for a `p`-cocycle `α` of `X` and a *normalized*
`q`-cocycle `β` of `Y` (one annihilating the degenerate `q`-simplices of `Y`), the pairing of the
cohomology cross product of their classes with the homology cross product of `x` and `y` is the
product of the pairings,

  `⟨α × β, x × y⟩ = ⟨α, x⟩ · ⟨β, y⟩`. -/
theorem kronH_homCrossLin (X Y : SSet) (p q : ℕ)
    (hX : ∀ n, Module.Projective ℤ ↥((sChain X).homology n))
    (hY : ∀ n, Module.Projective ℤ ↥((sChain Y).homology n))
    (x : ↥((sChain X).homology p)) (y : ↥((sChain Y).homology q))
    (α : Cochain ℤ X p) (β : Cochain ℤ Y q)
    (hα : cochainDiff ℤ X α = 0) (hβ : cochainDiff ℤ Y β = 0)
    (hn : ∀ z ∈ Y.degenerate q, genEval ℤ Y β z = 0)
    (hc : cochainDiff ℤ (sProd X Y) (crossCochain X Y p q α β) = 0) :
    kronH ℤ (sProd X Y) (p + q)
        (cohomologyClassOf ℤ (sProd X Y) (crossCochain X Y p q α β) hc)
        (homCrossLin X Y p q hX hY (x ⊗ₜ[ℤ] y))
      = kronH ℤ X p (cohomologyClassOf ℤ X α hα) x
        * kronH ℤ Y q (cohomologyClassOf ℤ Y β hβ) y := by
  rw [homCrossLin_tmul,
    show x = ((sChain X).homologyπ p).hom (homSec (sChain X) p (hX p) x) from
      (homSec_spec (sChain X) p (hX p) x).symm,
    show y = ((sChain Y).homologyπ q).hom (homSec (sChain Y) q (hY q) y) from
      (homSec_spec (sChain Y) q (hY q) y).symm]
  rw [kronH_apply, kronH_apply, kronH_apply]
  rw [iCycles_homCrossLin_tmul]
  rw [homSec_spec (sChain X) p (hX p) x, homSec_spec (sChain Y) q (hY q) y]
  exact crossCochain_ezChain X Y p q α β hn _ _

end

end Work.Kunneth
