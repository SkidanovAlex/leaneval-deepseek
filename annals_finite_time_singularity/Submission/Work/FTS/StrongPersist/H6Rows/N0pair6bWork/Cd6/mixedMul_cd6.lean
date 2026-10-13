/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Leibniz rule for `D_z^a D_θ^b` on `C^6` data on the open quadrant

`Work.Spaces.mixed a b h = D_z^a D_θ^b h`, where `D_z f = z ∂_z f` and
`D_θ f = sin(2θ) ∂_θ f`.  Both are derivations for the pointwise product, so

`D_z^a D_θ^b (f·g) = ∑_{i ≤ a} ∑_{j ≤ b} C(a,i) C(b,j) (D_z^i D_θ^j f)(D_z^{a-i} D_θ^{b-j} g)`

for `a + b ≤ 6`, whenever the uncurried `f` and `g` are `C^6` on the open quadrant
`Q0 = (0,∞) × (0,π/2)`.

This is the finite-order, *local* counterpart of `Work.FTS.GalBasis.ApproxCC.mixedMul`
(global `C^9`, `a + b ≤ 4`) and of `Work.Spaces.mixed_mul_eq` (`C^∞` on the open strip):
the hypotheses here are only of finite order and only on the open quadrant, so the
`DerivLike` machinery (which needs a class closed under the operators) does not apply,
and the two "function equalities" of the induction have to be read as *eventual*
equalities along the slices through the point.

The proof is a direct induction on the pair `(a,b)`:

* `D_z^a D_θ^b = D_z (D_z^{a-1} D_θ^b)` resp. `D_θ (D_z^a D_θ^{b-1})`;
* one application of the product rule for `D_z` resp. `D_θ` on each summand (which is why
  every summand of the induction hypothesis is rewritten to its expansion *near* the
  point first, via `Filter.EventuallyEq.deriv_eq`);
* the Pascal identity `Work.Spaces.leibniz_step` recombines the two shifted binomial sums.

The differentiability side conditions are discharged from `ContDiffOn ℝ 6` through
`Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le`: a mixed block
`D_z^j D_θ^i G` costs `i + j` orders, and inside the induction only blocks of total order
`≤ a + b - 1 ≤ 5` are ever differentiated.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalBasis.ApproxCC.mixedMul
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

set_option maxHeartbeats 1600000

/-! ## Product rule and linearity for `D_z` and `D_θ`

These are the pointwise derivatives of the two operators; the differentiability
hypotheses are the slices of the factors at the point under consideration. -/

private lemma cd6_Dz_mul {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hu : DifferentiableAt ℝ (fun z' => u z' θ) z)
    (hv : DifferentiableAt ℝ (fun z' => v z' θ) z) :
    Work.Spaces.Dz (fun z θ => u z θ * v z θ) z θ
      = Work.Spaces.Dz u z θ * v z θ + u z θ * Work.Spaces.Dz v z θ := by
  show z * deriv (fun z' : ℝ => u z' θ * v z' θ) z
      = z * deriv (fun z' : ℝ => u z' θ) z * v z θ
        + u z θ * (z * deriv (fun z' : ℝ => v z' θ) z)
  rw [show deriv (fun z' : ℝ => u z' θ * v z' θ) z
        = deriv ((fun z' : ℝ => u z' θ) * (fun z' : ℝ => v z' θ)) z from rfl]
  rw [deriv_mul hu hv]
  ring

private lemma cd6_Dz_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun z' => u z' θ) z)
    (hv : DifferentiableAt ℝ (fun z' => v z' θ) z) :
    Work.Spaces.Dz (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dz u z θ * v z θ + u z θ * Work.Spaces.Dz v z θ) := by
  show z * deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
      = cc * (z * deriv (fun z' : ℝ => u z' θ) z * v z θ
        + u z θ * (z * deriv (fun z' : ℝ => v z' θ) z))
  rw [show deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
        = deriv (fun y => cc * ((fun z' : ℝ => u z' θ) * (fun z' : ℝ => v z' θ)) y) z from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma cd6_Dz_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => A i z' θ) z) :
    Work.Spaces.Dz (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dz (A i) z θ := by
  have hfun : (fun z' : ℝ => ∑ i ∈ s, A i z' θ) = (∑ i ∈ s, fun z' : ℝ => A i z' θ) := by
    funext z'
    rw [Finset.sum_apply]
  show z * deriv (fun z' : ℝ => ∑ i ∈ s, A i z' θ) z
      = ∑ i ∈ s, z * deriv (fun z' : ℝ => A i z' θ) z
  rw [hfun, deriv_sum h, Finset.mul_sum]

private lemma cd6_Dth_mul {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hu : DifferentiableAt ℝ (fun θ' => u z θ') θ)
    (hv : DifferentiableAt ℝ (fun θ' => v z θ') θ) :
    Work.Spaces.Dth (fun z θ => u z θ * v z θ) z θ
      = Work.Spaces.Dth u z θ * v z θ + u z θ * Work.Spaces.Dth v z θ := by
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ' * v z θ') θ
      = Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ') θ * v z θ
        + u z θ * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => v z θ') θ)
  rw [show deriv (fun θ' : ℝ => u z θ' * v z θ') θ
        = deriv ((fun θ' : ℝ => u z θ') * (fun θ' : ℝ => v z θ')) θ from rfl]
  rw [deriv_mul hu hv]
  ring

private lemma cd6_Dth_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun θ' => u z θ') θ)
    (hv : DifferentiableAt ℝ (fun θ' => v z θ') θ) :
    Work.Spaces.Dth (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dth u z θ * v z θ + u z θ * Work.Spaces.Dth v z θ) := by
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
      = cc * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ') θ * v z θ
        + u z θ * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => v z θ') θ))
  rw [show deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
        = deriv (fun y => cc * ((fun θ' : ℝ => u z θ') * (fun θ' : ℝ => v z θ')) y) θ from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma cd6_Dth_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun θ' => A i z θ') θ) :
    Work.Spaces.Dth (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dth (A i) z θ := by
  have hfun : (fun θ' : ℝ => ∑ i ∈ s, A i z θ') = (∑ i ∈ s, fun θ' : ℝ => A i z θ') := by
    funext θ'
    rw [Finset.sum_apply]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => ∑ i ∈ s, A i z θ') θ
      = ∑ i ∈ s, Real.sin (2 * θ) * deriv (fun θ' : ℝ => A i z θ') θ
  rw [hfun, deriv_sum h, Finset.mul_sum]

private lemma cd6_differentiableAt_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {z : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) z) :
    DifferentiableAt ℝ (fun z' => ∑ i ∈ s, A i z') z := by
  have hfun : (fun z' => ∑ i ∈ s, A i z') = (∑ i ∈ s, A i) := by
    funext z'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

private lemma cd6_differentiableAt_sum_θ {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {θ : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) θ) :
    DifferentiableAt ℝ (fun θ' => ∑ i ∈ s, A i θ') θ := by
  have hfun : (fun θ' => ∑ i ∈ s, A i θ') = (∑ i ∈ s, A i) := by
    funext θ'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

/-! ## Congruence of `D_z` and `D_θ` under eventual equality of a slice

This is what makes the induction work in the local setting: the induction hypothesis is
available at *every* point of the open quadrant, hence on a whole slice through the
point under consideration, and `deriv` only sees an eventual equality
(`Filter.EventuallyEq.deriv_eq`, which needs no differentiability hypothesis). -/

private lemma cd6_Dz_congr {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun z' => u z' θ) =ᶠ[𝓝 z] (fun z' => v z' θ)) :
    Work.Spaces.Dz u z θ = Work.Spaces.Dz v z θ := by
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [Filter.EventuallyEq.deriv_eq h]

private lemma cd6_Dth_congr {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun θ' => u z θ') =ᶠ[𝓝 θ] (fun θ' => v z θ')) :
    Work.Spaces.Dth u z θ = Work.Spaces.Dth v z θ := by
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [Filter.EventuallyEq.deriv_eq h]

/-! ## The slices of the open quadrant through a point -/

private lemma cd6_zslice_mem {z θ : ℝ} (hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    {z' : ℝ | (z', θ) ∈ Work.FTS.EllipticEst.Q0} ∈ 𝓝 z := by
  have hset : {z' : ℝ | (z', θ) ∈ Work.FTS.EllipticEst.Q0} = Set.Ioi 0 := by
    ext z'
    rw [Set.mem_ofPred_eq, Work.FTS.EllipticEst.mem_Q0, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, hp.2.1, hp.2.2⟩⟩
  rw [hset]; exact isOpen_Ioi.mem_nhds hp.1

private lemma cd6_θslice_mem {z θ : ℝ} (hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    {θ' : ℝ | (z, θ') ∈ Work.FTS.EllipticEst.Q0} ∈ 𝓝 θ := by
  have hset : {θ' : ℝ | (z, θ') ∈ Work.FTS.EllipticEst.Q0} = Set.Ioo 0 (π / 2) := by
    ext θ'
    rw [Set.mem_ofPred_eq, Work.FTS.EllipticEst.mem_Q0, Set.mem_Ioo]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hp.1, h.1, h.2⟩⟩
  rw [hset]; exact isOpen_Ioo.mem_nhds ⟨hp.2.1, hp.2.2⟩

/-! ## The Leibniz rule -/

theorem mixedMul_cd6 {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ a b : ℕ, a + b ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ =
        ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ)) *
            (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
  have hQ0 : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  -- The mixed blocks of total order `≤ 5` have differentiable slices at every point of `Q0`.
  have hfz : ∀ i j : ℕ, i + j ≤ 5 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j f z' θ) z := by
    intro i j hij z θ hp
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      (n := 6) hQ0 j i 1 (by omega) hf
    exact Work.Spaces.differentiableAt_slice_fst
      ((h1.contDiffAt (hQ0.mem_nhds hp)).differentiableAt (by norm_num))
  have hfθ : ∀ i j : ℕ, i + j ≤ 5 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j f z θ') θ := by
    intro i j hij z θ hp
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      (n := 6) hQ0 j i 1 (by omega) hf
    exact Work.Spaces.differentiableAt_slice_snd
      ((h1.contDiffAt (hQ0.mem_nhds hp)).differentiableAt (by norm_num))
  have hgz : ∀ i j : ℕ, i + j ≤ 5 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j g z' θ) z := by
    intro i j hij z θ hp
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      (n := 6) hQ0 j i 1 (by omega) hg
    exact Work.Spaces.differentiableAt_slice_fst
      ((h1.contDiffAt (hQ0.mem_nhds hp)).differentiableAt (by norm_num))
  have hgθ : ∀ i j : ℕ, i + j ≤ 5 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j g z θ') θ := by
    intro i j hij z θ hp
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      (n := 6) hQ0 j i 1 (by omega) hg
    exact Work.Spaces.differentiableAt_slice_snd
      ((h1.contDiffAt (hQ0.mem_nhds hp)).differentiableAt (by norm_num))
  have key : ∀ n : ℕ, ∀ a b : ℕ, a + b ≤ n → a + b ≤ 6 →
      ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ =
        ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ)) *
            (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
    intro n
    induction n with
    | zero =>
        intro a b hsum h6 z θ hp
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha
        subst hb
        simp [Work.Spaces.mixed]
    | succ n ih =>
        intro a b hsum h6 z θ hp
        rcases Nat.eq_zero_or_pos a with ha | ha
        · -- `a = 0`: differentiate in `θ`
          subst ha
          rcases Nat.eq_zero_or_pos b with hb | hb
          · subst hb
            simp [Work.Spaces.mixed]
          · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            have hs : 0 + b' ≤ n := by omega
            have h6' : 0 + b' ≤ 6 := by omega
            have hslice := cd6_θslice_mem (z := z) (θ := θ) hp
            have hL : Work.Spaces.mixed 0 (b' + 1) (fun z θ => f z θ * g z θ) z θ
                = Work.Spaces.Dth (fun z θ => ∑ i ∈ Finset.range (0 + 1),
                    ∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ := by
              have h1 : Work.Spaces.mixed 0 (b' + 1) (fun z θ => f z θ * g z θ)
                  = Work.Spaces.Dth (Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ)) := by
                simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DzIter_zero]
              rw [h1]
              apply cd6_Dth_congr
              exact Filter.eventually_of_mem hslice (fun θ' hθ' => ih 0 b' hs h6' z θ' hθ')
            rw [hL]
            have hstep1 : Work.Spaces.Dth (fun z θ => ∑ i ∈ Finset.range (0 + 1),
                  ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ)) z θ
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i (j + 1) f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ) := by
              rw [cd6_Dth_sum (Finset.range (0 + 1))
                    (fun i z θ => ∑ j ∈ Finset.range (b' + 1),
                      (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun i hi => cd6_differentiableAt_sum_θ (Finset.range (b' + 1))
                      (fun j θ' => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ' * Work.Spaces.mixed (0 - i) (b' - j) g z θ'))
                      (fun j hj => ((hfθ i j (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ hp).mul
                        (hgθ (0 - i) (b' - j) (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ hp)).const_mul _))]
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [cd6_Dth_sum (Finset.range (b' + 1))
                    (fun j z θ => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun j hj => ((hfθ i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hp).mul
                      (hgθ (0 - i) (b' - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hp)).const_mul _)]
              refine Finset.sum_congr rfl fun j hj => ?_
              have hi0 : i = 0 := by have := Finset.mem_range.mp hi; omega
              rw [cd6_Dth_cmul (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ))
                    (hfθ i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hp)
                    (hgθ (0 - i) (b' - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hp)]
              rw [show Work.Spaces.Dth (Work.Spaces.mixed i j f) z θ
                    = Work.Spaces.mixed i (j + 1) f z θ from by
                    rw [show i = 0 from hi0]
                    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ,
                      Work.Spaces.DzIter_zero],
                  show Work.Spaces.Dth (Work.Spaces.mixed (0 - i) (b' - j) g) z θ
                    = Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ from by
                    rw [show i = 0 from hi0]
                    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ,
                      Work.Spaces.DzIter_zero, Nat.sub_zero]]
            have hstep2 : (∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ))
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1 + 1),
                    (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
              refine Finset.sum_congr rfl fun i hi => ?_
              have h1 : (∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ))
                  = ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1), (b'.choose j : ℝ) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ)) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              rw [h1, Work.Spaces.leibniz_step b' (fun j => Work.Spaces.mixed i j f z θ)
                    (fun m => Work.Spaces.mixed (0 - i) m g z θ)]
              have h2 : ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1 + 1),
                    ((b' + 1).choose j : ℝ) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ))
                  = ∑ j ∈ Finset.range (b' + 1 + 1),
                      (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              exact h2
            rw [hstep1, hstep2]
        · -- `a ≥ 1`: differentiate in `z`
          obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          have hs : a' + b ≤ n := by omega
          have h6' : a' + b ≤ 6 := by omega
          have hslice := cd6_zslice_mem (z := z) (θ := θ) hp
          have hL : Work.Spaces.mixed (a' + 1) b (fun z θ => f z θ * g z θ) z θ
              = Work.Spaces.Dz (fun z θ => ∑ i ∈ Finset.range (a' + 1),
                  ∑ j ∈ Finset.range (b + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ := by
            have h1 : Work.Spaces.mixed (a' + 1) b (fun z θ => f z θ * g z θ)
                = Work.Spaces.Dz (Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ)) := by
              simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
            rw [h1]
            apply cd6_Dz_congr
            exact Filter.eventually_of_mem hslice (fun z' hz' => ih a' b hs h6' z' θ hz')
          rw [hL]
          have hstep1 : Work.Spaces.Dz (fun z θ => ∑ i ∈ Finset.range (a' + 1),
                ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ)) z θ
              = ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed (i + 1) j f z θ
                      * Work.Spaces.mixed (a' - i) (b - j) g z θ
                    + Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ) := by
            rw [cd6_Dz_sum (Finset.range (a' + 1))
                  (fun i z θ => ∑ j ∈ Finset.range (b + 1),
                    ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun i hi => cd6_differentiableAt_sum (Finset.range (b + 1))
                    (fun j z' => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z' θ * Work.Spaces.mixed (a' - i) (b - j) g z' θ))
                    (fun j hj => ((hfz i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hp).mul
                      (hgz (a' - i) (b - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hp)).const_mul _))]
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [cd6_Dz_sum (Finset.range (b + 1))
                  (fun j z θ => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun j hj => ((hfz i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hp).mul
                    (hgz (a' - i) (b - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hp)).const_mul _)]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [cd6_Dz_cmul ((a'.choose i : ℝ) * (b.choose j : ℝ))
                  (hfz i j (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ hp)
                  (hgz (a' - i) (b - j) (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ hp)]
            rw [show Work.Spaces.Dz (Work.Spaces.mixed i j f) z θ
                  = Work.Spaces.mixed (i + 1) j f z θ from by
                  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ],
                show Work.Spaces.Dz (Work.Spaces.mixed (a' - i) (b - j) g) z θ
                  = Work.Spaces.mixed (a' - i + 1) (b - j) g z θ from by
                  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]]
          have hstep2 : (∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
              = ∑ i ∈ Finset.range (a' + 1 + 1), ∑ j ∈ Finset.range (b + 1),
                  ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ) := by
            have hkey1 := Finset.sum_comm (s := Finset.range (a' + 1))
              (t := Finset.range (b + 1))
              (f := fun i j => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                (Work.Spaces.mixed (i + 1) j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ
                  + Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
            have hkey2 := Finset.sum_comm (s := Finset.range (a' + 1 + 1))
              (t := Finset.range (b + 1))
              (f := fun i j => ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                (Work.Spaces.mixed i j f z θ
                  * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ))
            rw [hkey1, hkey2]
            refine Finset.sum_congr rfl fun j hj => ?_
            have h1 : (∑ i ∈ Finset.range (a' + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
                = (b.choose j : ℝ) * (∑ i ∈ Finset.range (a' + 1), (a'.choose i : ℝ) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [h1, Work.Spaces.leibniz_step a' (fun i => Work.Spaces.mixed i j f z θ)
                  (fun m => Work.Spaces.mixed m (b - j) g z θ)]
            have h2 : (b.choose j : ℝ) * (∑ i ∈ Finset.range (a' + 1 + 1),
                  ((a' + 1).choose i : ℝ) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ))
                = ∑ i ∈ Finset.range (a' + 1 + 1),
                    ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            exact h2
          rw [hstep1, hstep2]
  intro a b hab z θ hz hθ0 hθ1
  exact key (a + b) a b le_rfl hab z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
