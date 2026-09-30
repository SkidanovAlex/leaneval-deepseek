import Mathlib
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.kZchain
import Submission.Work.Pi6.EMM2.kZrangeModel
import Submission.Work.Pi6.EMM2.kZextend
import Submission.Work.Pi6.EMM2.hmapTwoSurjective
import Submission.Work.Pi6.EMODD.sphereClassReal
import Submission.Work.Pi6.EMODD.sphTwoPi
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.Serre.mpathQ_isSerreFibration
import Submission.Work.Serre.mpathQ_fibreHomeo
import Submission.Work.FGThm.mpathHomotopyEquiv
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.Serre.rwPiMapN_bijective_of_homotopyEquiv
import Submission.Work.Serre.isEMSpace_of_homotopyEquiv
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Pi6.EMODD.emSpaceTransport
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open scoped Topology

/-!
# `K(ℤ,2)` range models from a `K(ℤ/2,2)` range model through degree `8` (area EMM2)

The low-threshold variant (`N ≥ 8`) of `Work.Pi6.EMM2.kZmodel`, together with the fibre
calculation on which it rests.
-/

namespace Work.Pi6.EMM2

noncomputable section

/-! ## Group-theoretic preliminaries -/

theorem zmodTwoEqKZL (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  have hval : x.val = 0 ∨ x.val = 1 := by omega
  rcases hval with h | h
  · left
    have : ((x.val : ℕ) : ZMod 2) = ((0 : ℕ) : ZMod 2) := by rw [h]
    simpa using this
  · right
    have : ((x.val : ℕ) : ZMod 2) = ((1 : ℕ) : ZMod 2) := by rw [h]
    simpa using this

theorem multZModTwoEqKZL (m : Multiplicative (ZMod 2)) :
    m = 1 ∨ m = Multiplicative.ofAdd 1 := by
  rcases zmodTwoEqKZL (Multiplicative.toAdd m) with h | h
  · left
    refine Multiplicative.toAdd.injective ?_
    rw [show Multiplicative.toAdd m = 0 from h, toAdd_one]
  · right
    refine Multiplicative.toAdd.injective ?_
    rw [show Multiplicative.toAdd m = 1 from h, toAdd_ofAdd]

theorem ofAddOneNeOneKZL : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by
  rw [Ne, ofAdd_eq_one]
  decide

/-- Every element of `Multiplicative ℤ` is a power of the generator. -/
theorem ofAddOnePowToAddKZL (x : Multiplicative ℤ) :
    x = (Multiplicative.ofAdd (1 : ℤ)) ^ x.toAdd := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_zpow, toAdd_ofAdd]
  simp

/-- **The kernel of a non-trivial homomorphism `ℤ → ℤ/2` is `ℤ`.**  In the normalised form in
which the target element `ofAdd 1` is fixed. -/
theorem kerIsoIntKZL (ψ : Multiplicative ℤ →* Multiplicative (ZMod 2))
    (h1 : ψ (Multiplicative.ofAdd (1 : ℤ)) = Multiplicative.ofAdd (1 : ZMod 2)) :
    Nonempty (ψ.ker ≃* Multiplicative ℤ) := by
  -- `ψ` is the reduction mod `2` on `ofAdd n`
  have hψ : ∀ n : ℤ, ψ (Multiplicative.ofAdd n) = Multiplicative.ofAdd (n : ZMod 2) := by
    intro n
    have hpow : Multiplicative.ofAdd n = (Multiplicative.ofAdd (1 : ℤ)) ^ n := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_zpow, toAdd_ofAdd, toAdd_ofAdd]
      simp
    rw [hpow, map_zpow, h1, ← ofAdd_zsmul n (1 : ZMod 2), zsmul_one]
  -- membership in the kernel is divisibility by `2`
  have hmem : ∀ m : ℤ, Multiplicative.ofAdd m ∈ ψ.ker ↔ (2 : ℤ) ∣ m := by
    intro m
    rw [MonoidHom.mem_ker, hψ m, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd m 2]
    exact Iff.rfl
  -- the isomorphism `ℤ → ker ψ`, `m ↦ 2m`
  have hbij : Function.Bijective
      (fun m : Multiplicative ℤ =>
        (⟨Multiplicative.ofAdd (2 * m.toAdd), (hmem (2 * m.toAdd)).mpr ⟨m.toAdd, rfl⟩⟩ :
          ψ.ker)) := by
    constructor
    · intro a b hab
      have h3 : Multiplicative.ofAdd (2 * a.toAdd) = Multiplicative.ofAdd (2 * b.toAdd) :=
        congrArg Subtype.val hab
      have h4 : 2 * a.toAdd = 2 * b.toAdd := Multiplicative.ofAdd.injective h3
      have h5 : a.toAdd = b.toAdd := mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h4
      rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, h5]
    · intro y
      have hy : Multiplicative.ofAdd y.1.toAdd ∈ ψ.ker := by
        rw [ofAdd_toAdd]
        exact y.2
      obtain ⟨k, hk⟩ := (hmem y.1.toAdd).mp hy
      refine ⟨Multiplicative.ofAdd k, ?_⟩
      apply Subtype.ext
      show Multiplicative.ofAdd (2 * (Multiplicative.ofAdd k).toAdd) = y.1
      rw [toAdd_ofAdd, ← hk, ofAdd_toAdd]
  exact ⟨(MulEquiv.ofBijective
    ({ toFun := fun m : Multiplicative ℤ =>
         ⟨Multiplicative.ofAdd (2 * m.toAdd), (hmem (2 * m.toAdd)).mpr ⟨m.toAdd, rfl⟩⟩
       map_one' := by
         apply Subtype.ext
         show Multiplicative.ofAdd (2 * (1 : Multiplicative ℤ).toAdd) = 1
         rw [toAdd_one, mul_zero, ofAdd_zero]
       map_mul' := by
         intro a b
         apply Subtype.ext
         show Multiplicative.ofAdd (2 * (a * b).toAdd)
           = Multiplicative.ofAdd (2 * a.toAdd) * Multiplicative.ofAdd (2 * b.toAdd)
         rw [toAdd_mul, show 2 * (a.toAdd + b.toAdd) = 2 * a.toAdd + 2 * b.toAdd from by ring,
           ofAdd_add] } : Multiplicative ℤ →* ψ.ker) hbij).symm⟩

/-- A non-trivial homomorphism `φ : G → H` whose source is infinite cyclic and whose target has
order `2` has kernel `≅ ℤ` (the index-`2` subgroup `2ℤ ≤ ℤ`). -/
theorem kerMulEquivIntKZL {G H : Type} [Group G] [Group H] (e : G ≃* Multiplicative ℤ)
    (f : H ≃* Multiplicative (ZMod 2)) (φ : G →* H) (h : ∃ g : G, φ g ≠ 1) :
    Nonempty (φ.ker ≃* Multiplicative ℤ) := by
  classical
  -- normalise to `ψ : Multiplicative ℤ →* Multiplicative (ZMod 2)`
  let ψ : Multiplicative ℤ →* Multiplicative (ZMod 2) :=
    { toFun := fun x => f (φ (e.symm x))
      map_one' := by
        show f (φ (e.symm 1)) = 1
        rw [map_one, map_one, map_one]
      map_mul' := by
        intro a b
        show f (φ (e.symm (a * b))) = f (φ (e.symm a)) * f (φ (e.symm b))
        rw [map_mul, map_mul, map_mul] }
  -- `ψ` is non-trivial
  have hne : ψ (Multiplicative.ofAdd (1 : ℤ)) ≠ 1 := by
    intro hc
    obtain ⟨g, hg⟩ := h
    have h1 : ψ (e g) = 1 := by
      rw [ofAddOnePowToAddKZL (e g), map_zpow, hc, one_zpow]
    have hψeg : ψ (e g) = f (φ g) := by
      show f (φ (e.symm (e g))) = f (φ g)
      rw [MulEquiv.symm_apply_apply]
    rw [hψeg] at h1
    exact hg (f.injective (by rw [h1, map_one]))
  have h1 : ψ (Multiplicative.ofAdd (1 : ℤ)) = Multiplicative.ofAdd (1 : ZMod 2) := by
    rcases multZModTwoEqKZL (ψ (Multiplicative.ofAdd (1 : ℤ))) with hh | hh
    · exact absurd hh hne
    · exact hh
  obtain ⟨iso⟩ := kerIsoIntKZL ψ h1
  -- transport `φ.ker` to `ψ.ker` along `e`
  have htrans : Nonempty (φ.ker ≃* ψ.ker) := by
    let g' : φ.ker →* ψ.ker :=
      { toFun := fun x => ⟨e x.1, by
          have hx : φ x.1 = 1 := x.2
          show ψ (e x.1) = 1
          have hψx : ψ (e x.1) = f (φ x.1) := by
            show f (φ (e.symm (e x.1))) = f (φ x.1)
            rw [MulEquiv.symm_apply_apply]
          rw [hψx, hx, map_one]⟩
        map_one' := by
          apply Subtype.ext
          show e (1 : φ.ker).1 = 1
          rw [show (1 : φ.ker).1 = 1 from rfl, map_one]
        map_mul' := by
          intro a b
          apply Subtype.ext
          show e (a * b).1 = e a.1 * e b.1
          rw [show (a * b).1 = a.1 * b.1 from rfl, map_mul] }
    refine ⟨MulEquiv.ofBijective g' ⟨?_, ?_⟩⟩
    · intro a b hab
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val hab
    · intro y
      have hy : φ (e.symm y.1) = 1 := by
        have hsat : ψ y.1 = 1 := y.2
        have hψy : ψ y.1 = f (φ (e.symm y.1)) := rfl
        rw [hψy] at hsat
        exact f.injective (by rw [hsat, map_one])
      refine ⟨⟨e.symm y.1, hy⟩, ?_⟩
      apply Subtype.ext
      show e (e.symm y.1) = y.1
      rw [MulEquiv.apply_symm_apply]
  exact ⟨htrans.some.trans iso⟩


/-! ## The fibre of a Serre fibration between range models -/

/-- **The fibre of a Serre fibration over a `K(ℤ/2,2)` range model with total space a `K(ℤ,2)`
range model and `π₂`-surjective projection is a `K(ℤ,2)` range model one degree lower.**

Write `F = p ⁻¹' {p e₀}`.  The long exact homotopy sequence

`π₂(F) → π₂(E) → π₂(B) → π₁(F) → π₁(E) = 1` and `π_{i+1}(B) → π_i(F) → π_i(E) = 1` (`i ≥ 3`)

gives: `π₂(F) ≅ ker (π₂(E) → π₂(B)) ≅ ker (ℤ → ℤ/2) ≅ ℤ` (surjectivity of `π₂(p)` makes the
connecting map at `π₁(F)` trivial and `π₃(B) = 0` makes `π₂(F) → π₂(E)` injective), `π₁(F) = 0`
and `π_i(F) = 0` for `3 ≤ i ≤ N - 1`. -/
theorem fibreIsEMSpaceLowKZL {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (N : ℕ) (hN : 8 ≤ N)
    (hE : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N E e₀)
    (hB : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N B (p e₀))
    (hsurj : Function.Surjective (Work.StemsB.πmap p 1 e₀)) :
    Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) (N - 1)
      (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀) := by
  classical
  -- the long exact sequence in the two degrees needed
  obtain ⟨d0, hE0, hB0, hF0⟩ := Work.StemsB.fibrationLES_of_isSerreFibration p hp e₀ 0
  obtain ⟨d1, hE1, hB1, hF1⟩ := Work.StemsB.fibrationLES_of_isSerreFibration p hp e₀ 1
  -- the vanishing of the homotopy of the total space and of the base
  have hsubE : ∀ i : ℕ, i ≤ N → i ≠ 2 → Subsingleton (HomotopyGroup (Fin i) E e₀) :=
    fun i hi hne => hE.2 i hne (Or.inr hi)
  have hsubB : ∀ i : ℕ, i ≤ N → i ≠ 2 →
      Subsingleton (HomotopyGroup (Fin i) B (p e₀)) :=
    fun i hi hne => hB.2 i hne (Or.inr hi)
  -- `π₀`: the fibre is path connected (the base is `1`-connected)
  have hpcE : PathConnectedSpace E :=
    Work.StemsB.pathConnectedSpace_of_subsingleton_pi0 e₀
      (hE.2 0 (by norm_num) (Or.inl (by norm_num)))
  have hpcB : PathConnectedSpace B :=
    Work.StemsB.pathConnectedSpace_of_subsingleton_pi0 (p e₀)
      (hB.2 0 (by norm_num) (Or.inl (by norm_num)))
  have hpcF : PathConnectedSpace (Work.StemsB.fibre p (p e₀)) :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration p hp (p e₀) hpcE hpcB
      (hB.2 1 (by norm_num) (Or.inl (by norm_num)))
  -- `π₁` of the fibre vanishes
  have hker1 : ∀ y : HomotopyGroup (Fin 1) (Work.StemsB.fibre p (p e₀))
      (Work.StemsB.fibrePoint p e₀), y = 1 := by
    intro y
    haveI hsub : Subsingleton (HomotopyGroup (Fin (0 + 1)) E
        ((Work.StemsB.fibreIncl p (p e₀)) (Work.StemsB.fibrePoint p e₀))) :=
      hsubE 1 (by omega) (by norm_num)
    obtain ⟨x, hx⟩ := (hF0 y).mp (Subsingleton.elim
      ((Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 0
        (Work.StemsB.fibrePoint p e₀)) y) 1)
    rw [← hx, (hB0 x).mpr (hsurj x)]
  -- `π₂(F) → π₂(E)` is injective
  have hιinj : Function.Injective
      (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 1 (Work.StemsB.fibrePoint p e₀)) := by
    intro y z hyz
    haveI hsub : Subsingleton (HomotopyGroup (Fin (1 + 2)) B (p e₀)) :=
      hsubB 3 (by omega) (by norm_num)
    have hker : (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 1
        (Work.StemsB.fibrePoint p e₀)) (y * z⁻¹) = 1 := by
      rw [map_mul, map_inv, hyz, mul_inv_cancel]
    obtain ⟨w, hw⟩ := (hF1 (y * z⁻¹)).mp hker
    have hw1 : d1 w = 1 := by
      rw [show d1 w = d1 1 from congrArg d1 (Subsingleton.elim w 1), map_one]
    exact mul_inv_eq_one.mp (by rw [← hw, hw1])
  -- `π₂(F) ≅ ker (π₂ p)`
  have hisoKer : Nonempty (HomotopyGroup (Fin 2) (Work.StemsB.fibre p (p e₀))
      (Work.StemsB.fibrePoint p e₀) ≃* (Work.StemsB.πmap p 1 e₀).ker) := by
    let g : HomotopyGroup (Fin 2) (Work.StemsB.fibre p (p e₀))
        (Work.StemsB.fibrePoint p e₀) →* (Work.StemsB.πmap p 1 e₀).ker :=
      { toFun := fun y => ⟨(Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 1
            (Work.StemsB.fibrePoint p e₀)) y,
          (hE0 ((Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 1
            (Work.StemsB.fibrePoint p e₀)) y)).mpr ⟨y, rfl⟩⟩
        map_one' := by
          apply Subtype.ext
          show (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 1
            (Work.StemsB.fibrePoint p e₀)) 1 = 1
          rw [map_one]
        map_mul' := by
          intro a b
          apply Subtype.ext
          show (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 1
              (Work.StemsB.fibrePoint p e₀)) (a * b)
            = (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 1
                (Work.StemsB.fibrePoint p e₀)) a
              * (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 1
                (Work.StemsB.fibrePoint p e₀)) b
          rw [map_mul] }
    have hg : Function.Bijective ⇑g := by
      constructor
      · intro a b hab
        exact hιinj (congrArg Subtype.val hab)
      · intro y
        obtain ⟨a, ha⟩ := (hE0 y.1).mp y.2
        exact ⟨a, Subtype.ext ha⟩
    exact ⟨MulEquiv.ofBijective g hg⟩
  -- and its identification with `ℤ`
  have htwo : Nonempty (HomotopyGroup (Fin 2) (Work.StemsB.fibre p (p e₀))
      (Work.StemsB.fibrePoint p e₀) ≃* Multiplicative ℤ) := by
    obtain ⟨eE⟩ := hE.1
    obtain ⟨eB⟩ := hB.1
    have hnt : ∃ g : HomotopyGroup (Fin 2) E e₀, (Work.StemsB.πmap p 1 e₀) g ≠ 1 := by
      obtain ⟨g, hg⟩ := hsurj (eB.symm (Multiplicative.ofAdd 1))
      refine ⟨g, ?_⟩
      rw [hg]
      intro hcontra
      exact ofAddOneNeOneKZL (eB.symm.injective (by rw [hcontra, map_one]))
    obtain ⟨iso2⟩ := kerMulEquivIntKZL eE eB (Work.StemsB.πmap p 1 e₀) hnt
    exact ⟨hisoKer.some.trans iso2⟩
  -- vanishing in degrees `3, …, N - 1`
  have hvan : ∀ k : ℕ, k + 3 ≤ N - 1 →
      Subsingleton (HomotopyGroup (Fin (k + 3)) (Work.StemsB.fibre p (p e₀))
        (Work.StemsB.fibrePoint p e₀)) := by
    intro k hk
    obtain ⟨d, -, -, hdF⟩ := Work.StemsB.fibrationLES_of_isSerreFibration p hp e₀ (k + 2)
    haveI hsub₁ : Subsingleton (HomotopyGroup (Fin (k + 2 + 1)) E
        ((Work.StemsB.fibreIncl p (p e₀)) (Work.StemsB.fibrePoint p e₀))) :=
      hsubE (k + 3) (by omega) (by omega)
    haveI hsub₂ : Subsingleton (HomotopyGroup (Fin (k + 2 + 2)) B (p e₀)) :=
      hsubB (k + 4) (by omega) (by omega)
    refine ⟨fun y z => ?_⟩
    have hy : y = 1 := by
      obtain ⟨w, hw⟩ := (hdF y).mp (Subsingleton.elim
        ((Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) (k + 2)
          (Work.StemsB.fibrePoint p e₀)) y) 1)
      rw [← hw, show d w = d 1 from congrArg d (Subsingleton.elim w 1), map_one]
    have hz : z = 1 := by
      obtain ⟨w, hw⟩ := (hdF z).mp (Subsingleton.elim
        ((Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) (k + 2)
          (Work.StemsB.fibrePoint p e₀)) z) 1)
      rw [← hw, show d w = d 1 from congrArg d (Subsingleton.elim w 1), map_one]
    rw [hy, hz]
  refine ⟨htwo, ?_⟩
  intro i hi hc
  rcases lt_or_ge i 2 with hlt | hge
  · interval_cases i
    · haveI : Subsingleton (ZerothHomotopy (Work.StemsB.fibre p (p e₀))) :=
        (pathConnectedSpace_iff_zerothHomotopy).mp hpcF |>.2
      exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy
        (X := Work.StemsB.fibre p (p e₀)) (x := Work.StemsB.fibrePoint p e₀)).injective
          (Subsingleton.elim _ _)⟩
    · exact ⟨fun a b => by rw [hker1 a, hker1 b]⟩
  · have hi3 : 3 ≤ i := by omega
    have hiN : i ≤ N - 1 := hc.resolve_left (by omega)
    have hieq : i = (i - 3) + 3 := by omega
    rw [hieq]
    exact hvan (i - 3) (by omega)


/-! ## The `K(ℤ,2)` model through degree `8` -/

/-- **`π₂` of the `2`-sphere is `ℤ` at every base point.** -/
theorem sphereTwoPiBaseKZL (s : Work.Stems.sphere 2) :
    Nonempty (HomotopyGroup (Fin 2) (Work.Stems.sphere 2) s ≃* Multiplicative ℤ) := by
  have hconn : ∀ i : ℕ, i < 1 + 1 →
      Subsingleton (HomotopyGroup (Fin i) (Work.Stems.sphere 2) s) :=
    fun i hi => Work.Stems.sphereConnectivity 2 i (by omega) s
  obtain ⟨e⟩ := Work.Pi6.EMODD.hurewiczMulEquivSpheres (X := Work.Stems.sphere 2) s 1 le_rfl hconn
  obtain ⟨h⟩ := Work.Cohomology.sphereHomologyTop 2 (by norm_num)
  exact ⟨e.trans (AddEquiv.toMultiplicative h.toLinearEquiv.toAddEquiv)⟩

theorem kZmodelLow : Work.Pi6.EMM2.KZModelLowStatement := by
  intro X inst x₀ N hN hX
  classical
  -- the `π₂ ≅ ℤ/2` isomorphism of the model at the base point
  obtain ⟨φ⟩ := hX.1
  -- a non-trivial class of `π₂(X,x₀)` and a based map `f : S² → X` realising it
  have ha : φ.symm (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by
    intro h
    have h1 : φ (φ.symm (Multiplicative.ofAdd (1 : ZMod 2))) = φ 1 := congrArg φ h
    rw [MulEquiv.apply_symm_apply, MulEquiv.map_one] at h1
    exact ofAddOneNeOneKZL h1
  obtain ⟨f, s₀, hfs₀, c, hc⟩ :=
    Work.Pi6.EMODD.sphereClassReal 1 le_rfl (X := X) (x₀ := x₀)
      (φ.symm (Multiplicative.ofAdd (1 : ZMod 2))) ha
  -- `S²` is `1`-connected, with `π₂ ≅ ℤ`
  have hS0 : Subsingleton (HomotopyGroup (Fin 0) (Work.Stems.sphere 2) s₀) :=
    Work.Stems.sphereConnectivity 2 0 (by norm_num) s₀
  have hS1 : Subsingleton (HomotopyGroup (Fin 1) (Work.Stems.sphere 2) s₀) :=
    Work.Stems.sphereConnectivity 2 1 (by norm_num) s₀
  obtain ⟨eS⟩ := sphereTwoPiBaseKZL s₀
  -- `X` is path connected, hence has no homotopy in degrees `3, …, N` at *any* point
  haveI hXpc : PathConnectedSpace X :=
    Work.StemsB.pathConnectedSpace_of_subsingleton_pi0 x₀
      (hX.2 0 (by norm_num) (Or.inl (by norm_num)))
  have hXvan : ∀ (z : X) (i : ℕ), 3 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) X z) := by
    intro z i h3 hiN
    exact Work.EMFG.subsingleton_homotopyGroup_of_joined' (PathConnectedSpace.joined x₀ z) i
      (by omega) (hX.2 i (by omega) (Or.inr hiN))
  -- the extension of `f` over the `K(ℤ,2)` model
  obtain ⟨r, hr⟩ := kZextend (Y := Work.Stems.sphere 2) (Z := X) N (by omega) f hXvan
  -- `kZ S² (N-2)` is a range model of `K(ℤ,2)` through `N`
  have hKZ : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N
      (Work.Pi6.EMM2.kZ (Work.Stems.sphere 2) (N - 2))
      (Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2) s₀) :=
    kZrangeModel s₀ N (by omega) hS0 hS1 ⟨eS⟩
  -- the two maps `r ∘ kZUp` and `f` agree, and the base points `r k₀` and `f s₀` are equal
  have hs' : r ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀) = f s₀ :=
    congrArg (fun k : C(Work.Stems.sphere 2, X) => k s₀) hr
  have hr0 : r ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀) = x₀ := hs'.trans hfs₀
  -- surjectivity of `π₂(f)` from the non-triviality of `f`
  have eφ : HomotopyGroup (Fin 2) X (f s₀) ≃* Multiplicative (ZMod 2) :=
    (Work.StemsB.homotopyGroupCast hfs₀ 1).trans φ
  have hsurj_f : Function.Surjective (Work.StemsB.πmap f 1 s₀) := by
    intro y
    rcases multZModTwoEqKZL (eφ y) with hy | hy
    · refine ⟨1, ?_⟩
      have hy1 : y = 1 := by
        have h2 := congrArg eφ.symm hy
        simpa using h2
      rw [hy1, map_one]
    · refine ⟨c, ?_⟩
      have hcc : eφ (Work.StemsB.πmap f 1 s₀ c) = eφ y := by
        rcases multZModTwoEqKZL (eφ (Work.StemsB.πmap f 1 s₀ c)) with h' | h'
        · exact absurd (eφ.injective (by rw [h', map_one])) hc
        · rw [h', hy]
      exact eφ.injective hcc
  -- `π₂(r)` is onto at `k₀`
  have hfac : ∀ a : HomotopyGroup (Fin 2) (Work.Stems.sphere 2) s₀,
      (Work.StemsB.homotopyGroupCast hs' 1)
          (Work.StemsB.πmap r 1 ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)
            (Work.StemsB.πmap (Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) 1 s₀ a))
        = Work.StemsB.πmap f 1 s₀ a := by
    intro a
    rw [← Work.StemsB.πmap_comp_apply (Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) r 1 s₀ a]
    exact Work.StemsB.πmap_congr hr 1 s₀ a
  have hsurj_r : Function.Surjective
      (Work.StemsB.πmap r 1 ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)) := by
    intro y
    obtain ⟨a, ha'⟩ := hsurj_f ((Work.StemsB.homotopyGroupCast hs' 1) y)
    refine ⟨Work.StemsB.πmap (Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) 1 s₀ a, ?_⟩
    have h1 : (Work.StemsB.homotopyGroupCast hs' 1)
        (Work.StemsB.πmap r 1 ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)
          (Work.StemsB.πmap (Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) 1 s₀ a)) =
        (Work.StemsB.homotopyGroupCast hs' 1) y := by
      rw [hfac a, ha']
    exact (Work.StemsB.homotopyGroupCast hs' 1).injective h1
  -- the range model of `X` at the base point `r k₀`
  have hXr : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X
      (r ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)) := by
    rw [hr0]; exact hX
  -- the fibre of the mapping-path fibration is a `K(ℤ,2)` range model through `N - 1`
  have hFib : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) (N - 1)
      (Work.StemsB.fibre (Work.Serre.mpathQ r)
        (r ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)))
      (Work.StemsB.fibrePoint (Work.Serre.mpathQ r)
        (Work.Serre.mpathOf r ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀))) := by
    have hmaps : (Work.Serre.mpathQ r).comp (Work.Serre.mpathOf r) = r := rfl
    -- `π₂` of the projection `mpathQ r` is onto, since it factors `π₂(r)` through the section
    have hcomp2 : ∀ a, (Work.StemsB.πmap (Work.Serre.mpathQ r) 1
          (Work.Serre.mpathOf r ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)))
          ((Work.StemsB.πmap (Work.Serre.mpathOf r) 1
            ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)) a)
        = (Work.StemsB.πmap r 1 ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)) a := by
      intro a
      rw [← Work.StemsB.πmap_comp_apply (Work.Serre.mpathOf r) (Work.Serre.mpathQ r) 1 _ a]
      exact Work.StemsB.πmap_congr hmaps 1 _ a
    refine fibreIsEMSpaceLowKZL (Work.Serre.mpathQ r) (Work.Serre.mpathQ_isSerreFibration r)
      (Work.Serre.mpathOf r ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)) N hN
      ?_ ?_ ?_
    · -- the total space of the mapping-path fibration is a `K(ℤ,2)` range model
      have h1 : ((Work.Serre.mpathFst r).comp (Work.Serre.mpathOf r)).Homotopic
          (ContinuousMap.id (Work.Pi6.EMM2.kZ (Work.Stems.sphere 2) (N - 2))) := by
        have h : (Work.Serre.mpathFst r).comp (Work.Serre.mpathOf r) =
            ContinuousMap.id (Work.Pi6.EMM2.kZ (Work.Stems.sphere 2) (N - 2)) := by
          ext e
          rfl
        rw [h]
      exact Work.Pi6.EMODD.emSpaceTransport ℤ 2 (by norm_num) N
        ({ toFun := Work.Serre.mpathOf r
           invFun := Work.Serre.mpathFst r
           left_inv := h1
           right_inv := Work.FGThm.mpathOf_comp_mpathFst_homotopic r } :
          ContinuousMap.HomotopyEquiv (Work.Pi6.EMM2.kZ (Work.Stems.sphere 2) (N - 2))
            (Work.Serre.mpath r)) rfl hKZ
    · exact hXr
    · intro y
      obtain ⟨a, ha⟩ := hsurj_r y
      exact ⟨(Work.StemsB.πmap (Work.Serre.mpathOf r) 1
        ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)) a, by rw [hcomp2 a, ha]⟩
  refine ⟨Work.Pi6.EMM2.kZ (Work.Stems.sphere 2) (N - 2),
    Work.Pi6.EMM2.kZTop (Work.Stems.sphere 2) (N - 2),
    (Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀, r, ?_, ?_, ?_, ?_, ?_⟩
  · exact hr0
  · exact hKZ
  · exact hsurj_r
  · exact hmapTwoSurjective r ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)
      N (by omega) hKZ hXr hsurj_r
  · exact hFib

end

end Work.Pi6.EMM2
