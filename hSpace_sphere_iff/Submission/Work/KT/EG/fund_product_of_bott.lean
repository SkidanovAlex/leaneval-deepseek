import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.k0_basic
import Submission.Work.KT.bott_aux
import Submission.Work.KT.ExtProdB
import Submission.Work.KT.ExtGen.Basic

namespace Work.KT.EG

/-! ## Two unit laws for an `IsK0Mul` product

`K0` carries no `Ring` instance in this development, but the product on `K₀` is characterised on
generators (`IsK0Mul`), and `k0_basic` produces a product with that characterisation together with
its unit laws; uniqueness of the characterising property transports them.  (These replay
`Work.KT.Bott.pf_IsK0Mul_unique` / `pf_IsK0Mul_one` inside the imports of this module.) -/

/-- Two products on `K₀ A` with the defining property of the ring product agree. -/
lemma fpBot_IsK0Mul_unique {A : Type} [Ring A] {μ μ' : K0 A →+ K0 A →+ K0 A}
    (hμ : IsK0Mul μ) (hμ' : IsK0Mul μ') : μ = μ' := by
  refine AddMonoidHom.ext fun x => ?_
  refine Work.KT.ep_hom_ext_cls (μ x) (μ' x) fun p _ => ?_
  have h1 : μ.flip (cls p) = μ'.flip (cls p) := by
    refine Work.KT.ep_hom_ext_cls _ _ fun q _ => ?_
    simp only [AddMonoidHom.flip_apply]
    rw [hμ q p, hμ' q p]
  exact congrFun (congrArg DFunLike.coe h1) x

/-- The unit laws of an `IsK0Mul` product on `K₀ A`. -/
lemma fpBot_IsK0Mul_unit (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x)
    {μ : K0 A →+ K0 A →+ K0 A} (hμ : IsK0Mul μ) :
    (∀ a, μ (cls (Mat.one A 1)) a = a) ∧ ∀ a, μ a (cls (Mat.one A 1)) = a := by
  obtain ⟨μ0, hμ0, hcomm0, -, hunit0⟩ := Work.KT.k0_basic.1 A hcomm
  have h := fpBot_IsK0Mul_unique hμ hμ0
  subst h
  exact ⟨hunit0, fun a => by rw [hcomm0 a (cls (Mat.one A 1))]; exact hunit0 a⟩


/-- **Assembly of the fundamental product from the Bott statements.**

Write `s := fst*` (the pullback along `X × S² → X`), `γ := snd* (cls hopfIdem)`,
`β := γ - cls (Mat.one C(X × S², ℂ) 1)`, so `Φ (a,b) = s a + μ (s b) γ`.  If `r` is a retraction
along `s` (`hrs`), multiplicative for the products `μ` and `μX` (`hrmul`), sends `γ` to the class of
the trivial bundle (`hγ`), has kernel the image of the Bott map `b ↦ μ (s b) β` (`hker`), and that
map is injective (`hinj`), then `Φ` is bijective.

This is the last step of the route note in `Submission/Work/KT/Fund/NOTES_kappa.md` (§0.3, §5):
take `r` to be the restriction to the fibre over a base point of `S²`.

Surjectivity: `y := z - s (r z)` is killed by `r`, so `y = μ (s b) β = μ (s b) γ - s b`
(unit law `μ x (cls 1) = x`), whence `z = Φ (r z - b, b)`.

Injectivity: `r (Φ a b) = a + b` by `hrs`, `hrmul`, `hγ` and the unit law `μX x (cls 1) = x`, so
`Φ a b = 0` gives `a = -b`; then `μ (s b) β = Φ (-b) b = 0`, so `b = 0` by `hinj` and `a = 0`.
The two unit laws follow from `IsK0Mul` by `mulCls_of_idem` and the homomorphism-extension lemma
`ExtProdB.ep_hom_ext_cls` (`K0.addHom_ext` in `k0_basic` also suffices; `Bott.prodAlg_free`'s
`pf_IsK0Mul_one` is a usable template).  (`K0` carries no `Ring` instance in this development, so
the unit laws are stated with `cls (Mat.one _ 1)`.) -/
theorem fund_product_of_bott (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (hμ : IsK0Mul μ)
    (μX : K0 C(X, ℂ) →+ K0 C(X, ℂ) →+ K0 C(X, ℂ)) (hμX : IsK0Mul μX)
    (r : K0 C(X × S2, ℂ) →+ K0 C(X, ℂ))
    (hrs : ∀ a : K0 C(X, ℂ), r (K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ))
      (pullAlg (ContinuousMap.fst : C(X × S2, X))) a) = a)
    (hrmul : ∀ x y : K0 C(X × S2, ℂ), r (μ x y) = μX (r x) (r y))
    (hγ : r (K0.mapA (A := C(S2, ℂ)) (B := C(X × S2, ℂ))
      (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem)) = cls (Mat.one C(X, ℂ) 1))
    (hker : ∀ y : K0 C(X × S2, ℂ), r y = 0 → ∃ b : K0 C(X, ℂ),
      y = μ (K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ))
        (pullAlg (ContinuousMap.fst : C(X × S2, X))) b)
        (K0.mapA (A := C(S2, ℂ)) (B := C(X × S2, ℂ))
          (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem) - cls (Mat.one C(X × S2, ℂ) 1)))
    (hinj : ∀ b : K0 C(X, ℂ), μ (K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ))
      (pullAlg (ContinuousMap.fst : C(X × S2, X))) b)
      (K0.mapA (A := C(S2, ℂ)) (B := C(X × S2, ℂ))
        (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem) - cls (Mat.one C(X × S2, ℂ) 1)) = 0 →
      b = 0) :
    Function.Bijective (fun ab : K0 C(X, ℂ) × K0 C(X, ℂ) =>
      K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ)) (pullAlg (ContinuousMap.fst : C(X × S2, X))) ab.1 +
        μ (K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ)) (pullAlg (ContinuousMap.fst : C(X × S2, X))) ab.2)
          (K0.mapA (A := C(S2, ℂ)) (B := C(X × S2, ℂ))
            (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem))) := by
  -- Abbreviate the pull-back `s`, the Hopf class `γ` and the two unit classes.
  set s := K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ)) (pullAlg (ContinuousMap.fst : C(X × S2, X)))
  set γ := K0.mapA (A := C(S2, ℂ)) (B := C(X × S2, ℂ))
    (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem)
  set eC := cls (Mat.one C(X × S2, ℂ) 1) with heC
  set eX := cls (Mat.one C(X, ℂ) 1) with heX
  -- The two unit laws of the products, and the retraction `r` computed on `Φ`.
  have hcommA : ∀ x y : C(X × S2, ℂ), x * y = y * x := fun x y => mul_comm x y
  have hcommX : ∀ x y : C(X, ℂ), x * y = y * x := fun x y => mul_comm x y
  obtain ⟨_, hunitR⟩ := fpBot_IsK0Mul_unit (C(X × S2, ℂ)) hcommA hμ
  obtain ⟨_, hunitXR⟩ := fpBot_IsK0Mul_unit (C(X, ℂ)) hcommX hμX
  have hunitR' : ∀ x : K0 C(X × S2, ℂ), μ x eC = x := by
    intro x; rw [heC]; exact hunitR x
  have hunitXR' : ∀ x : K0 C(X, ℂ), μX x eX = x := by
    intro x; rw [heX]; exact hunitXR x
  -- `r ∘ Φ = fst + snd`
  have hrΦ : ∀ a b, r (s a + μ (s b) γ) = a + b := by
    intro a b
    rw [map_add, hrs, hrmul, hrs, hγ, hunitXR']
  -- Vanishing of `Φ` forces `a = b = 0`.
  have hzero : ∀ a b : K0 C(X, ℂ), s a + μ (s b) γ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 : a + b = 0 := by
      have h := hrΦ a b
      rw [hab, map_zero] at h
      exact h.symm
    have ha : a = -b := eq_neg_of_add_eq_zero_left h1
    have h2 : s (-b) + μ (s b) γ = 0 := by rw [← ha]; exact hab
    have h3 : - s b + μ (s b) γ = 0 := by simpa using h2
    have hsb : μ (s b) γ = s b := (neg_add_eq_zero.mp h3).symm
    have hb0 : b = 0 := by
      refine hinj b ?_
      rw [map_sub, hunitR', hsb, sub_self]
    exact ⟨by rw [ha, hb0, neg_zero], hb0⟩
  refine ⟨?_, ?_⟩
  · -- injectivity: reduce to `hzero` on the difference
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : s a + μ (s b) γ = s a' + μ (s b') γ := by simpa using hab
    have hsub : s (a - a') + μ (s (b - b')) γ = 0 := by
      have hkey : s (a - a') + μ (s (b - b')) γ
          = (s a + μ (s b) γ) - (s a' + μ (s b') γ) := by
        rw [map_sub, map_sub, map_sub, AddMonoidHom.sub_apply]
        abel
      rw [hkey, hab', sub_self]
    obtain ⟨ha, hb⟩ := hzero (a - a') (b - b') hsub
    simp only [Prod.mk.injEq]
    exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb⟩
  · -- surjectivity: `z - s (r z)` lies in the kernel of `r`
    intro z
    obtain ⟨b, hb⟩ := hker (z - s (r z)) (by rw [map_sub, hrs, sub_self])
    refine ⟨(r z - b, b), ?_⟩
    have hb' : z - s (r z) = μ (s b) γ - s b := by
      rw [hb, map_sub, hunitR']
    have hz' : z = μ (s b) γ - s b + s (r z) := sub_eq_iff_eq_add.mp hb'
    show s (r z - b) + μ (s b) γ = z
    calc s (r z - b) + μ (s b) γ
        = s (r z) - s b + μ (s b) γ := by rw [map_sub]
      _ = μ (s b) γ - s b + s (r z) := by abel
      _ = z := hz'.symm


end Work.KT.EG
