import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.Spaces.mixed_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys.GdotAux

set_option maxHeartbeats 1600000

/-!
# The Leibniz rule for `D_z^j D_θ^i` at finite order on an open set

`Work.Spaces.mixed j i f = D_z^j D_θ^i f`, where `D_z f = z ∂_z f` and `D_θ f = sin(2θ) ∂_θ f`
are derivations for the pointwise product, so the iterated Leibniz rule

`D_z^j D_θ^i (f·h) = ∑_{a ≤ i} ∑_{b ≤ j} C(i,a) C(j,b) (D_z^b D_θ^a f)(D_z^{j-b} D_θ^{i-a} h)`

holds.  Here it is proved for `f`, `h` that are jointly `C^{j+i}` on an *arbitrary open* set
`V ⊆ ℝ²`, at a point of `V`; the consumer
`Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_mul_le2` specialises it to `V = Q0` and `C²` data.

The proof is the direct induction on the pair `(a,b)`: `D_z^a D_θ^b = D_z (D_z^{a-1} D_θ^b)`
resp. `D_θ (D_z^a D_θ^{b-1})`, one application of the product rule for `D_z` resp. `D_θ`, and
the Pascal identity `Work.Spaces.leibniz_step` to recombine the two shifted binomial sums.
The differentiability side conditions are discharged from the local `C^{a+b}` hypothesis
through `Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le` (every mixed
block costs its total order in regularity), and the induction hypothesis, which holds only on
`V`, is transported across `D_z`/`D_θ` by the locality of the derivative on the open set `V`.
-/

/-! ## Pointwise product rules and linearity for `D_z` and `D_θ` -/

private lemma Dz_mul {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
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

private lemma Dz_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun z' => u z' θ) z)
    (hv : DifferentiableAt ℝ (fun z' => v z' θ) z) :
    Work.Spaces.Dz (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dz u z θ * v z θ + u z θ * Work.Spaces.Dz v z θ) := by
  show z * deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
      = cc * (z * deriv (fun z' : ℝ => u z' θ) z * v z θ
        + u z θ * (z * deriv (fun z' : ℝ => v z' θ) z))
  rw [show deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
        = deriv (fun y => cc * ((fun z' : ℝ => u z' θ) * (fun z' : ℝ => v z' θ)) y) z
        from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma Dz_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => A i z' θ) z) :
    Work.Spaces.Dz (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dz (A i) z θ := by
  have hfun : (fun z' : ℝ => ∑ i ∈ s, A i z' θ) = (∑ i ∈ s, fun z' : ℝ => A i z' θ) := by
    funext z'
    rw [Finset.sum_apply]
  show z * deriv (fun z' : ℝ => ∑ i ∈ s, A i z' θ) z
      = ∑ i ∈ s, z * deriv (fun z' : ℝ => A i z' θ) z
  rw [hfun, deriv_sum h, Finset.mul_sum]

private lemma Dth_mul {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
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

private lemma Dth_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun θ' => u z θ') θ)
    (hv : DifferentiableAt ℝ (fun θ' => v z θ') θ) :
    Work.Spaces.Dth (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dth u z θ * v z θ + u z θ * Work.Spaces.Dth v z θ) := by
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
      = cc * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ') θ * v z θ
        + u z θ * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => v z θ') θ))
  rw [show deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
        = deriv (fun y => cc * ((fun θ' : ℝ => u z θ') * (fun θ' : ℝ => v z θ')) y) θ
        from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma Dth_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun θ' => A i z θ') θ) :
    Work.Spaces.Dth (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dth (A i) z θ := by
  have hfun : (fun θ' : ℝ => ∑ i ∈ s, A i z θ') = (∑ i ∈ s, fun θ' : ℝ => A i z θ') := by
    funext θ'
    rw [Finset.sum_apply]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => ∑ i ∈ s, A i z θ') θ
      = ∑ i ∈ s, Real.sin (2 * θ) * deriv (fun θ' : ℝ => A i z θ') θ
  rw [hfun, deriv_sum h, Finset.mul_sum]

private lemma differentiableAt_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {z : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) z) :
    DifferentiableAt ℝ (fun z' => ∑ i ∈ s, A i z') z := by
  have hfun : (fun z' => ∑ i ∈ s, A i z') = (∑ i ∈ s, A i) := by
    funext z'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

private lemma differentiableAt_sum_θ {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {θ : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) θ) :
    DifferentiableAt ℝ (fun θ' => ∑ i ∈ s, A i θ') θ := by
  have hfun : (fun θ' => ∑ i ∈ s, A i θ') = (∑ i ∈ s, A i) := by
    funext θ'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

/-! ## Locality of `D_z` and `D_θ` on an open set -/

private lemma Dz_congr_of_eqOn {V : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ∀ p ∈ V, f p.1 p.2 = g p.1 p.2) :
    ∀ p ∈ V, Work.Spaces.Dz f p.1 p.2 = Work.Spaces.Dz g p.1 p.2 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have htend : Tendsto (fun z' : ℝ => ((z', θ) : ℝ × ℝ)) (𝓝 z) (𝓝 (z, θ)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hmem : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) := by
    filter_upwards [htend.eventually (hV.mem_nhds hp)] with z' hz'
    exact h (z', θ) hz'
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hmem.deriv_eq]

private lemma Dth_congr_of_eqOn {V : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ∀ p ∈ V, f p.1 p.2 = g p.1 p.2) :
    ∀ p ∈ V, Work.Spaces.Dth f p.1 p.2 = Work.Spaces.Dth g p.1 p.2 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have htend : Tendsto (fun θ' : ℝ => ((z, θ') : ℝ × ℝ)) (𝓝 θ) (𝓝 (z, θ)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hmem : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    filter_upwards [htend.eventually (hV.mem_nhds hp)] with θ' hθ'
    exact h (z, θ') hθ'
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hmem.deriv_eq]

/-! ## Differentiability of the mixed blocks at a point of `V` -/

private lemma diffAt_mixed_z {N : ℕ} {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ N (Function.uncurry F) V) {i j : ℕ} (hij : i + j + 1 ≤ N)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j F z' θ) z := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed i j F)) V :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le hV j i 1 (by omega) hF
  have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed i j F)) (z, θ) :=
    (h1.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hz)
  exact Work.Spaces.differentiableAt_slice_fst hd

private lemma diffAt_mixed_θ {N : ℕ} {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ N (Function.uncurry F) V) {i j : ℕ} (hij : i + j + 1 ≤ N)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j F z θ') θ := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed i j F)) V :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le hV j i 1 (by omega) hF
  have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed i j F)) (z, θ) :=
    (h1.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hz)
  exact Work.Spaces.differentiableAt_slice_snd hd

/-! ## The finite-order Leibniz rule -/

theorem mixedMulFinAuxLocal {N : ℕ} {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ N (Function.uncurry f) V)
    (hg : ContDiffOn ℝ N (Function.uncurry g) V) :
    ∀ a b : ℕ, a + b ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
  have hfz : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j f z' θ) z :=
    fun i j hij z θ hz => diffAt_mixed_z hV hf hij hz
  have hgz : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j g z' θ) z :=
    fun i j hij z θ hz => diffAt_mixed_z hV hg hij hz
  have hfθ : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j f z θ') θ :=
    fun i j hij z θ hz => diffAt_mixed_θ hV hf hij hz
  have hgθ : ∀ i j : ℕ, i + j + 1 ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j g z θ') θ :=
    fun i j hij z θ hz => diffAt_mixed_θ hV hg hij hz
  have key : ∀ n : ℕ, ∀ a b : ℕ, a + b ≤ n → a + b ≤ N → ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
    intro n
    induction n with
    | zero =>
        intro a b hsum hN z θ hz
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha
        subst hb
        simp [Work.Spaces.mixed]
    | succ n ih =>
        intro a b hsum hN z θ hz
        rcases Nat.eq_zero_or_pos a with ha | ha
        · subst ha
          rcases Nat.eq_zero_or_pos b with hb | hb
          · subst hb
            simp [Work.Spaces.mixed]
          · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            have hs : 0 + b' ≤ n := by omega
            have hN' : 0 + b' ≤ N := by omega
            have hEqOn : ∀ p ∈ V,
                Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ) p.1 p.2
                  = (fun z θ => ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                      (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ)) p.1 p.2 :=
              fun p hp => ih 0 b' hs hN' p.1 p.2 hp
            have hL : Work.Spaces.mixed 0 (b' + 1) (fun z θ => f z θ * g z θ) z θ
                = Work.Spaces.Dth
                    (Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ)) z θ := by
              simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DzIter_zero]
            have hcong := Dth_congr_of_eqOn
              (f := Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ))
              (g := fun z θ => ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
              hV hEqOn (z, θ) hz
            rw [hL, hcong]
            have hstep1 : Work.Spaces.Dth (fun z θ => ∑ i ∈ Finset.range (0 + 1),
                  ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (0 - i) (b' - j) g z θ)) z θ
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i (j + 1) f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ) := by
              rw [Dth_sum (Finset.range (0 + 1))
                    (fun i z θ => ∑ j ∈ Finset.range (b' + 1),
                      (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun i hi => differentiableAt_sum_θ (Finset.range (b' + 1))
                      (fun j θ' => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ'
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ'))
                      (fun j hj => ((hfθ i j (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ hz).mul
                        (hgθ (0 - i) (b' - j) (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ hz)).const_mul _))]
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [Dth_sum (Finset.range (b' + 1))
                    (fun j z θ => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun j hj => ((hfθ i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz).mul
                      (hgθ (0 - i) (b' - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz)).const_mul _)]
              refine Finset.sum_congr rfl fun j hj => ?_
              have hi0 : i = 0 := by have := Finset.mem_range.mp hi; omega
              rw [Dth_cmul (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ))
                    (hfθ i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz)
                    (hgθ (0 - i) (b' - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz)]
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
                  = ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1),
                      (b'.choose j : ℝ) *
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
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ))
                  = ∑ j ∈ Finset.range (b' + 1 + 1),
                      (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              exact h2
            rw [hstep1, hstep2]
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          have hs : a' + b ≤ n := by omega
          have hN' : a' + b ≤ N := by omega
          have hEqOn : ∀ p ∈ V,
              Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ) p.1 p.2
                = (fun z θ => ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                    ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ)) p.1 p.2 :=
            fun p hp => ih a' b hs hN' p.1 p.2 hp
          have hL : Work.Spaces.mixed (a' + 1) b (fun z θ => f z θ * g z θ) z θ
              = Work.Spaces.Dz
                  (Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ)) z θ := by
            simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
          have hcong := Dz_congr_of_eqOn
            (f := Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ))
            (g := fun z θ => ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ))
            hV hEqOn (z, θ) hz
          rw [hL, hcong]
          have hstep1 : Work.Spaces.Dz (fun z θ => ∑ i ∈ Finset.range (a' + 1),
                ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ)) z θ
              = ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed (i + 1) j f z θ
                      * Work.Spaces.mixed (a' - i) (b - j) g z θ
                    + Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ) := by
            rw [Dz_sum (Finset.range (a' + 1))
                  (fun i z θ => ∑ j ∈ Finset.range (b + 1),
                    ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun i hi => differentiableAt_sum (Finset.range (b + 1))
                    (fun j z' => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z' θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z' θ))
                    (fun j hj => ((hfz i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz).mul
                      (hgz (a' - i) (b - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hz)).const_mul _))]
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Dz_sum (Finset.range (b + 1))
                  (fun j z θ => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun j hj => ((hfz i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz).mul
                    (hgz (a' - i) (b - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hz)).const_mul _)]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Dz_cmul ((a'.choose i : ℝ) * (b.choose j : ℝ))
                  (hfz i j (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ hz)
                  (hgz (a' - i) (b - j) (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ hz)]
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
  intro a b hab z θ hz
  exact key (a + b) a b le_rfl hab z θ hz

/-! ## The requested statement -/

theorem mixedMulFinLocal {j i : ℕ} {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V)
    (hf : ContDiffOn ℝ (j + i) (Function.uncurry f) V)
    (hg : ContDiffOn ℝ (j + i) (Function.uncurry g) V) :
    ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) := by
  intro z θ hz
  have h := mixedMulFinAuxLocal (N := j + i) hV hf hg j i le_rfl z θ hz
  rw [h]
  have h2 : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ))
      = ∑ b ∈ Finset.range (j + 1), ∑ a ∈ Finset.range (i + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) :=
    Finset.sum_comm
  rw [h2]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
  ring


end Work.FTS_RegExport.RXT.Sys.GdotAux
