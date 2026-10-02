import Mathlib
import Submission.Work.Serre.C1Loop
import Submission.Work.Serre.C1SphOne
import Submission.Work.StemsB.PiMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# C1: a map `S¹ → X` realising `π₁(X) ≅ ℤ`

This is step (2.1) of the C1 assembly: for a based space `(X, pt)` whose fundamental group is
infinite cyclic, there is a map `φ : S¹ → X` carrying `sphOneBase` to `pt` and inducing a
*bijection* on `π₁` — the map that the mapping-cylinder argument of `Work.Serre.C1Pair` needs.

The construction is the descent of a representative loop `γ` of a generator of `π₁(X, pt)`:

* `homotopyGroupCast_apply_mk` — transport of a class along an equality of base points, computed on
  representatives;
* `injective_of_surjective_of_mulEquiv_int` — a surjective homomorphism between infinite cyclic
  groups is injective (so that it suffices to prove that the induced map hits a generator);
* `exists_sphOne_map_piMap_bijective` — the result.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

/-- **Transport of a class along an equality of base points, on representatives.**  If `α` and `β`
are generalized loops with the *same underlying continuous map* but based at `x` and `y`
respectively, then the transport of the class of `α` along `h : x = y` is the class of `β`. -/
theorem homotopyGroupCast_apply_mk {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y) (n : ℕ)
    (α : Ω^ (Fin (n + 1)) X x) (β : Ω^ (Fin (n + 1)) X y) (hαβ : ⇑α.1 = ⇑β.1) :
    Work.StemsB.homotopyGroupCast h n (Quotient.mk _ α) = Quotient.mk _ β := by
  cases h
  exact congrArg (Quotient.mk _) (Subtype.ext (ContinuousMap.ext (funext_iff.mp hαβ)))

/-- **A surjective homomorphism between infinite cyclic groups is injective.**  With `eG : G ≃* ℤ`
and `eH : H ≃* ℤ`, a surjection `f : G →* H` maps a generator of `G` to a generator of `H`, which
therefore has infinite order; hence nothing nontrivial lies in the kernel. -/
theorem injective_of_surjective_of_mulEquiv_int {G H : Type*} [Group G] [Group H]
    (eG : G ≃* Multiplicative ℤ) (eH : H ≃* Multiplicative ℤ) (f : G →* H)
    (hf : Function.Surjective f) : Function.Injective f := by
  obtain ⟨g, hg⟩ := exists_generator_of_mulEquiv_int eG
  obtain ⟨h, hh⟩ := exists_generator_of_mulEquiv_int eH
  -- the image of a generator is a generator (surjectivity)
  have hgen : ∀ b : H, ∃ m : ℤ, b = (f g) ^ m := by
    intro b
    obtain ⟨y, hy⟩ := hf b
    obtain ⟨m, hm⟩ := (hg y).exists
    exact ⟨m, by rw [← hy, hm, map_zpow]⟩
  -- hence `f g` has infinite order: `f g = h ^ n` with `n * k = 1`, so `n = ±1`
  obtain ⟨n, hn⟩ := (hh (f g)).exists
  obtain ⟨k, hk⟩ := hgen h
  have hnk : n * k = 1 := by
    rw [hn, ← zpow_mul] at hk
    exact (hh h).unique hk (by rw [zpow_one])
  have hunit : n = 1 ∨ n = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hnk
  intro x y hxy
  have hker : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
  obtain ⟨m, hm⟩ := (hg (x * y⁻¹)).exists
  have hfm : (f g) ^ m = 1 := by rw [← map_zpow, ← hm, hker]
  have hm0 : m = 0 := by
    rcases hunit with hn1 | hn1
    · rw [hn1, zpow_one] at hn
      rw [hn] at hfm
      have h2 : h = h ^ (m + 1) := by rw [zpow_add, hfm, one_mul, zpow_one]
      have h3 : m + 1 = 1 := (hh h).unique h2 (by rw [zpow_one])
      omega
    · rw [hn, hn1, ← zpow_mul, neg_one_mul] at hfm
      have h2 : h = h ^ ((-m) + 1) := by rw [zpow_add, hfm, one_mul, zpow_one]
      have h3 : (-m) + 1 = 1 := (hh h).unique h2 (by rw [zpow_one])
      omega
  have h1 : x * y⁻¹ = 1 := by rw [hm, hm0, zpow_zero]
  exact mul_inv_eq_one.mp h1

/-- **A map `S¹ → X` realising `π₁ ≅ ℤ`.**  If `π₁(X, pt) ≅ ℤ`, there is a continuous map
`φ : S¹ → X` with `φ sphOneBase = pt` inducing a bijection `π₁(S¹) → π₁(X, pt)`.

Proof: take a based loop `γ` representing a generator `c` of `π₁(X,pt)`, view it as a loop on `[0,1]`
and descend it to `S¹` (`loopToSphOne`).  On the class of the standard parametrization the induced
map is `c` up to the transport along `φ sphOneBase = pt`, so its image contains a generator, i.e. it
is surjective; injectivity follows from `injective_of_surjective_of_mulEquiv_int`. -/
theorem exists_sphOne_map_piMap_bijective (X : Type) [TopologicalSpace X] (pt : X)
    (e : HomotopyGroup (Fin 1) X pt ≃* Multiplicative ℤ) :
    ∃ φ : C(Work.Serre.Sph 1, X), φ Work.Serre.sphOneBase = pt ∧
      Function.Bijective (Work.StemsB.πmap φ 0 Work.Serre.sphOneBase) := by
  obtain ⟨c, hc⟩ := exists_generator_of_mulEquiv_int e
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(GenLoop (Fin 1) X pt), Quotient.mk _ γ = c :=
    ⟨Quotient.out c, Quotient.out_eq c⟩
  have hγ0 : γ.1 (fun _ : Fin 1 => (0 : unitInterval)) = pt := γ.2 _ ⟨0, Or.inl rfl⟩
  have hγ1 : γ.1 (fun _ : Fin 1 => (1 : unitInterval)) = pt := γ.2 _ ⟨0, Or.inr rfl⟩
  -- the loop `[0,1] → X` underlying `γ`
  let cI : C(unitInterval, Fin 1 → unitInterval) :=
    ⟨fun u _ => u, continuous_pi fun _ => continuous_id⟩
  let γ' : C(unitInterval, X) := γ.1.comp cI
  have hγ'0 : γ' 0 = pt := hγ0
  have hγ'1 : γ' 1 = pt := hγ1
  have hloop : γ' 0 = γ' 1 := hγ'0.trans hγ'1.symm
  have hφ : loopToSphOne γ' hloop sphOneBase = pt :=
    (loopToSphOne_apply γ' hloop 0).trans hγ'0
  -- the class of the parametrization maps to `c`, after transporting the base point
  have hkey : ⇑(Work.StemsB.genLoopMap (loopToSphOne γ' hloop) 1 s1ParamLoop).1 = ⇑γ.1 := by
    funext y
    show (loopToSphOne γ' hloop) (s1ParamCubeCM y) = γ.1 y
    rw [s1ParamCubeCM_apply, loopToSphOne_apply]
    show γ.1 (fun _ : Fin 1 => y 0) = γ.1 y
    have h1 : (fun _ : Fin 1 => y 0) = y := by
      funext i
      show y 0 = y i
      rw [Subsingleton.elim i 0]
    rw [h1]
  have hmain : Work.StemsB.homotopyGroupCast hφ 0
      (Work.StemsB.πmap (loopToSphOne γ' hloop) 0 sphOneBase ⟦s1ParamLoop⟧) = c := by
    rw [Work.StemsB.πmap_apply_mk]
    exact (homotopyGroupCast_apply_mk hφ 0 _ γ hkey).trans hγ
  let lam : HomotopyGroup (Fin 1) (Work.Serre.Sph 1) sphOneBase := ⟦s1ParamLoop⟧
  have hlam : Work.StemsB.πmap (loopToSphOne γ' hloop) 0 sphOneBase lam
      = ⟦Work.StemsB.genLoopMap (loopToSphOne γ' hloop) 1 s1ParamLoop⟧ := rfl
  have hsurj : Function.Surjective
      (Work.StemsB.πmap (loopToSphOne γ' hloop) 0 sphOneBase) := by
    intro b
    have hsymm : (Work.StemsB.homotopyGroupCast hφ 0).symm c
        = Work.StemsB.πmap (loopToSphOne γ' hloop) 0 sphOneBase lam :=
      (Work.StemsB.homotopyGroupCast hφ 0).injective
        (by rw [MulEquiv.apply_symm_apply, hmain])
    obtain ⟨m, hm⟩ := (hc (Work.StemsB.homotopyGroupCast hφ 0 b)).exists
    refine ⟨lam ^ m, ?_⟩
    rw [map_zpow, ← hsymm, ← map_zpow, ← hm, MulEquiv.symm_apply_apply]
  refine ⟨loopToSphOne γ' hloop, hφ, ?_, hsurj⟩
  refine injective_of_surjective_of_mulEquiv_int ?_ ?_ _ hsurj
  · exact (multiplicativeAdditiveSelf _).symm.trans
      (AddEquiv.toMultiplicative (Classical.choice (pi1SphOne_addEquiv_int sphOneBase)))
  · exact (Work.StemsB.homotopyGroupCast hφ 0).trans e

end

end Work.Serre
