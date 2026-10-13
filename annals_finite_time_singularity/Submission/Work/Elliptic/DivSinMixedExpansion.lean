import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.DthIter_contDiffAt
import Submission.Work.Spaces.DzIterSmoothOn
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Congruence of the slice derivatives on an open set

`pz`, `pth`, `Dz`, `Dth` are local operators, so functions that agree on an open set `V`
have equal images under them at every point of `V`.  The analogues for the fixed set
`nbhU` of `SmoothNbhd` live in `Submission.Work.Spaces.mixed_comm`. -/

/-- Congruence of `pz` under `EqOn` on an open set. -/
private lemma pz_congrOn {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) {p : ℝ × ℝ} (hp : p ∈ V) :
    pz g p.1 p.2 = pz g' p.1 p.2 := by
  have hnb : ∀ᶠ z' in 𝓝 p.1, (z', p.2) ∈ V :=
    (Continuous.prodMk_left p.2).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun z' => Function.uncurry g (z', p.2)) =ᶠ[𝓝 p.1]
      (fun z' => Function.uncurry g' (z', p.2)) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  have := hslice.deriv_eq
  simpa only [pz, Function.uncurry] using this

/-- Congruence of `Dz` under `EqOn` on an open set. -/
private lemma Dz_congrOn {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Dz g)) (Function.uncurry (Dz g')) V := by
  intro p hp
  have hpz := pz_congrOn hV h hp
  show p.1 * pz g p.1 p.2 = p.1 * pz g' p.1 p.2
  rw [hpz]

/-- Congruence of `Dth` under `EqOn` on an open set. -/
private lemma Dth_congrOn {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Dth g)) (Function.uncurry (Dth g')) V := by
  intro p hp
  have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ V :=
    (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun θ' => Function.uncurry g (p.1, θ')) =ᶠ[𝓝 p.2]
      (fun θ' => Function.uncurry g' (p.1, θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  have hd := hslice.deriv_eq
  exact congrArg (fun t => Real.sin (2 * p.2) * t) hd

/-- Congruence of `DthIter` under `EqOn` on an open set. -/
private lemma DthIter_congrOn {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (i : ℕ) :
    Set.EqOn (Function.uncurry (DthIter i g)) (Function.uncurry (DthIter i g')) V := by
  induction i with
  | zero => exact h
  | succ i ih => simpa only [DthIter_succ] using Dth_congrOn hV ih

/-! ## The main commutation -/

/-- `D_z^j` commutes with `D_θ^i` followed by multiplication by a function of `θ` alone,
on any open set on which `f` is `C^∞` and the `θ`-factor is `C^∞`. -/
theorem mixed_div_comm {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ} {c : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) V)
    (hc : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => c p.2) V) :
    ∀ j i : ℕ,
      Set.EqOn (Function.uncurry (DzIter j (DthIter i (fun z θ => f z θ * c θ))))
        (Function.uncurry (DthIter i (fun z θ => DzIter j f z θ * c θ))) V := by
  intro j
  induction j with
  | zero =>
      intro i
      exact fun p hp => rfl
  | succ j ih =>
      intro i p hp
      have hg : ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => DzIter j f z θ * c θ)) V :=
        (DzIterSmoothOn hV hf j).mul hc
      have hstep2 : Dz (DzIter j (DthIter i (fun z θ => f z θ * c θ))) p.1 p.2
          = Dz (DthIter i (fun z θ => DzIter j f z θ * c θ)) p.1 p.2 :=
        Dz_congrOn hV (ih i) hp
      have hstep3 : Dz (DthIter i (fun z θ => DzIter j f z θ * c θ)) p.1 p.2
          = DthIter i (Dz (fun z θ => DzIter j f z θ * c θ)) p.1 p.2 :=
        DzDthIterCommOn hV hg i hp
      have hstep4 : Set.EqOn (Function.uncurry (Dz (fun z θ => DzIter j f z θ * c θ)))
          (Function.uncurry (fun z θ => DzIter (j + 1) f z θ * c θ)) V := by
        intro q hq
        show q.1 * pz (fun z θ => DzIter j f z θ * c θ) q.1 q.2
            = DzIter (j + 1) f q.1 q.2 * c q.2
        have hfun : (fun z' => DzIter j f z' q.2 * c q.2)
            = (fun z' => c q.2 * DzIter j f z' q.2) := by funext z'; ring
        show q.1 * deriv (fun z' => DzIter j f z' q.2 * c q.2) q.1
            = DzIter (j + 1) f q.1 q.2 * c q.2
        rw [hfun, deriv_const_mul_field]
        rw [show DzIter (j + 1) f q.1 q.2 = q.1 * deriv (fun z' => DzIter j f z' q.2) q.1
              from rfl]
        ring
      have hstep5 : DthIter i (Dz (fun z θ => DzIter j f z θ * c θ)) p.1 p.2
          = DthIter i (fun z θ => DzIter (j + 1) f z θ * c θ) p.1 p.2 :=
        DthIter_congrOn hV hstep4 i hp
      calc DzIter (j + 1) (DthIter i (fun z θ => f z θ * c θ)) p.1 p.2
          = Dz (DzIter j (DthIter i (fun z θ => f z θ * c θ))) p.1 p.2 := rfl
        _ = Dz (DthIter i (fun z θ => DzIter j f z θ * c θ)) p.1 p.2 := hstep2
        _ = DthIter i (Dz (fun z θ => DzIter j f z θ * c θ)) p.1 p.2 := hstep3
        _ = DthIter i (fun z θ => DzIter (j + 1) f z θ * c θ) p.1 p.2 := hstep5

end Work.Spaces

namespace Work.Elliptic

set_option autoImplicit false

/-- `1 / sin(2θ)`, as a function of `θ` alone. -/
private def invSin2 : ℝ → ℝ := fun θ => (Real.sin (2 * θ))⁻¹

/-- An open neighbourhood of the domain on which `1 / sin(2θ)` is `C^∞`. -/
private def Vnbh : Set (ℝ × ℝ) :=
  Set.Ioi (-1) ×ˢ
    (Set.Ioo (-1) (Real.pi / 2 + 1) ∩ (fun t : ℝ => Real.sin (2 * t)) ⁻¹' {y : ℝ | y ≠ 0})

private lemma isOpen_Vnbh : IsOpen Vnbh := by
  rw [Vnbh]
  exact isOpen_Ioi.prod (isOpen_Ioo.inter
    (isOpen_ne.preimage (by continuity : Continuous fun t : ℝ => Real.sin (2 * t))))

private lemma Vnbh_subset : Vnbh ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) := by
  intro p hp
  rw [Vnbh, Set.mem_prod] at hp
  rw [Set.mem_prod]
  exact ⟨hp.1, hp.2.1⟩

/-- `D_z^j` commutes with `D_θ^i` across division by `sin(2θ)`: on the domain
`[0,∞) × (0,π/2)`, applying `D_z^j` after dividing by `sin 2θ` and applying `D_θ^i`
gives the same function as dividing `D_z^j Φ` by `sin 2θ` and then applying `D_θ^i`. -/
theorem DivSinMixedExpansion (Φ : ℝ → ℝ → ℝ) (hΦ : Work.Spaces.SmoothNbhd Φ) (j i : ℕ)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter j
        (Work.Spaces.DthIter i (fun z θ => Φ z θ / Real.sin (2 * θ))) z θ
      = Work.Spaces.DthIter i
          (fun z θ => Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ)) z θ := by
  have hz' : (-1 : ℝ) < z := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz; linarith
  have hθ₁ : (-1 : ℝ) < θ := by linarith [hθ.1]
  have hθ₂ : θ < Real.pi / 2 + 1 := by linarith [hθ.2, Real.pi_pos]
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hp : (z, θ) ∈ Vnbh := by
    rw [Vnbh, Set.mem_prod, Set.mem_inter_iff, Set.mem_Ioo, Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨hz', ⟨hθ₁, hθ₂⟩, hsin⟩
  have hf : ContDiffOn ℝ ⊤ (Function.uncurry Φ) Vnbh := hΦ.mono Vnbh_subset
  have hc : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => invSin2 p.2) Vnbh := by
    have hsin_s : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Vnbh :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hne : ∀ p ∈ Vnbh, Real.sin (2 * p.2) ≠ 0 := by
      intro p hp'
      rw [Vnbh, Set.mem_prod, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hp'
      exact hp'.2.2
    exact hsin_s.inv hne
  have key := Work.Spaces.mixed_div_comm isOpen_Vnbh hf hc j i hp
  simpa only [invSin2, div_eq_mul_inv, Function.uncurry] using key

end Work.Elliptic
