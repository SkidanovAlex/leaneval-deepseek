import Mathlib
import Submission.Work.Pi6.EMM2.Defs
import Submission.Work.Pi6.EMM2.kZchain
import Submission.Work.Pi6.EMM2.kZrangeModel
import Submission.Work.Pi6.EMM2.kZextend
import Submission.Work.Pi6.EMODD.fibreOfMpathQ
import Submission.Work.Pi6.EMM2.hmapTwoSurjective
import Submission.Work.Pi6.EMODD.sphereClassReal
import Submission.Work.Pi6.EMODD.sphTwoPi
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Cohomology.sphereHomologyTop
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# Area EMM2: the `K(ℤ,2)` model covering a `K(ℤ/2,2)` range model

Given a range model `X` of `K(ℤ/2,2)` through `N ≥ 10` we produce the range model
`Kℤ = Work.Pi6.EMM2.kZ (S²) (N-2)` of `K(ℤ,2)` through `N` (the `2`-sphere with `π₃, …, π_N`
killed) together with a based map `r : Kℤ → X` onto on `π₂` — the reduction map along which the
mod-2 forcing argument of `Work.Pi6.emMod2` runs.

Assembly:
* `Work.Pi6.EMODD.sphereClassReal` realises a non-trivial class of `π₂(X,x₀)` by a based map
  `f : S² → X` which is non-trivial on `π₂`;
* `Work.Pi6.EMM2.kZextend` extends `f` over `kZ S² (N-2)` (the target `X` has `π_i = 0` for
  `3 ≤ i ≤ N`);
* `Work.Pi6.EMM2.kZrangeModel` makes `kZ S² (N-2)` a range model of `K(ℤ,2)` through `N`;
* `Work.Pi6.EMM2.hmapTwoSurjective` upgrades `π₂`-surjectivity of `r` to `H₂(−;ℤ)`-surjectivity;
* `Work.Pi6.EMM2.mpathFibreModel` computes the fibre of the mapping-path fibration `mpathQ r`.
-/

open scoped Topology

namespace Work.Pi6.EMM2

noncomputable section

/-- **`π₂` of the `2`-sphere is `ℤ` at every base point** (`Hurewicz` in the first non-vanishing
degree plus `H₂(S²;ℤ) ≅ ℤ`). -/
theorem sphereTwoPiBase (s : Work.Stems.sphere 2) :
    Nonempty (HomotopyGroup (Fin 2) (Work.Stems.sphere 2) s ≃* Multiplicative ℤ) := by
  have hconn : ∀ i : ℕ, i < 1 + 1 →
      Subsingleton (HomotopyGroup (Fin i) (Work.Stems.sphere 2) s) :=
    fun i hi => Work.Stems.sphereConnectivity 2 i (by omega) s
  obtain ⟨e⟩ := Work.Pi6.EMODD.hurewiczMulEquivSpheres (X := Work.Stems.sphere 2) s 1 le_rfl hconn
  obtain ⟨h⟩ := Work.Cohomology.sphereHomologyTop 2 (by norm_num)
  exact ⟨e.trans (AddEquiv.toMultiplicative h.toLinearEquiv.toAddEquiv)⟩

/-- `ZMod 2` has exactly the two elements `0`, `1`. -/
theorem zmodTwo_eq (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  have hval : x.val = 0 ∨ x.val = 1 := by omega
  rcases hval with h | h
  · left
    have : ((x.val : ℕ) : ZMod 2) = ((0 : ℕ) : ZMod 2) := by rw [h]
    simpa using this
  · right
    have : ((x.val : ℕ) : ZMod 2) = ((1 : ℕ) : ZMod 2) := by rw [h]
    simpa using this

/-- `Multiplicative (ZMod 2)` has exactly the two elements `1` and `ofAdd 1`. -/
theorem multZModTwo_eq (m : Multiplicative (ZMod 2)) :
    m = 1 ∨ m = Multiplicative.ofAdd 1 := by
  rcases zmodTwo_eq (Multiplicative.toAdd m) with h | h
  · left
    refine Multiplicative.toAdd.injective ?_
    rw [show Multiplicative.toAdd m = 0 from h, toAdd_one]
  · right
    refine Multiplicative.toAdd.injective ?_
    rw [show Multiplicative.toAdd m = 1 from h, toAdd_ofAdd]

/-- `ofAdd 1 ≠ 1` in `Multiplicative (ZMod 2)`. -/
theorem ofAdd_one_ne_one : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by
  rw [Ne, ofAdd_eq_one]
  decide

theorem kZmodel {X : Type} [TopologicalSpace X] (x₀ : X) (N : ℕ) (hN : 10 ≤ N)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀) :
    ∃ (KZ : Type) (tKZ : TopologicalSpace KZ) (k₀ : KZ)
      (r : @ContinuousMap KZ X tKZ (inferInstance : TopologicalSpace X)),
      letI : TopologicalSpace KZ := tKZ
      r k₀ = x₀ ∧
      Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N KZ k₀ ∧
      Function.Surjective (Work.StemsB.πmap r 1 k₀) ∧
      Function.Surjective (Work.Pi6.hmap ℤ r 2).hom ∧
      Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) (N - 1)
        (Work.StemsB.fibre (Work.Serre.mpathQ r) (r k₀))
        (Work.StemsB.fibrePoint (Work.Serre.mpathQ r) (Work.Serre.mpathOf r k₀)) := by
  classical
  -- the `π₂ ≅ ℤ/2` isomorphism of the model at the base point
  obtain ⟨φ⟩ := hX.1
  -- a non-trivial class of `π₂(X,x₀)` and a based map `f : S² → X` realising it
  have ha : φ.symm (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by
    intro h
    have h1 : φ (φ.symm (Multiplicative.ofAdd (1 : ZMod 2))) = φ 1 := congrArg φ h
    rw [MulEquiv.apply_symm_apply, MulEquiv.map_one] at h1
    exact ofAdd_one_ne_one h1
  obtain ⟨f, s₀, hfs₀, c, hc⟩ :=
    Work.Pi6.EMODD.sphereClassReal 1 le_rfl (X := X) (x₀ := x₀)
      (φ.symm (Multiplicative.ofAdd (1 : ZMod 2))) ha
  -- `S²` is `1`-connected, with `π₂ ≅ ℤ`
  have hS0 : Subsingleton (HomotopyGroup (Fin 0) (Work.Stems.sphere 2) s₀) :=
    Work.Stems.sphereConnectivity 2 0 (by norm_num) s₀
  have hS1 : Subsingleton (HomotopyGroup (Fin 1) (Work.Stems.sphere 2) s₀) :=
    Work.Stems.sphereConnectivity 2 1 (by norm_num) s₀
  obtain ⟨eS⟩ := sphereTwoPiBase s₀
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
    rcases multZModTwo_eq (eφ y) with hy | hy
    · refine ⟨1, ?_⟩
      have hy1 : y = 1 := by
        have h2 := congrArg eφ.symm hy
        simpa using h2
      rw [hy1, map_one]
    · refine ⟨c, ?_⟩
      have hcc : eφ (Work.StemsB.πmap f 1 s₀ c) = eφ y := by
        rcases multZModTwo_eq (eφ (Work.StemsB.πmap f 1 s₀ c)) with h' | h'
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
  -- a non-trivial value of `π₂(r)`, as needed by the fibre computation
  have hnt_r : ∃ b : HomotopyGroup (Fin 2) (Work.Pi6.EMM2.kZ (Work.Stems.sphere 2) (N - 2))
      ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀),
      Work.StemsB.πmap r 1 ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀) b ≠ 1 := by
    refine ⟨Work.StemsB.πmap (Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) 1 s₀ c, ?_⟩
    intro h
    have h1 := hfac c
    rw [h, map_one] at h1
    exact hc h1.symm
  -- the range model of `X` at the base point `r k₀`
  have hXr : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X
      (r ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)) := by
    rw [hr0]; exact hX
  refine ⟨Work.Pi6.EMM2.kZ (Work.Stems.sphere 2) (N - 2),
    Work.Pi6.EMM2.kZTop (Work.Stems.sphere 2) (N - 2),
    (Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀, r, ?_, ?_, ?_, ?_, ?_⟩
  · exact hr0
  · exact hKZ
  · exact hsurj_r
  · exact hmapTwoSurjective r ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀)
      N (by omega) hKZ hXr hsurj_r
  · exact (Work.Pi6.EMODD.fibreOfMpathQ N hN r
      ((Work.Pi6.EMM2.kZUp (Work.Stems.sphere 2) (N - 2)) s₀) hKZ hXr hnt_r).1

end

end Work.Pi6.EMM2
