/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/mixed_Jeps.lean` — `J_ε` commutes with every `D_z^j D_θ^i`

This is the iterated form of **E1** of the design (`FTS_HARD_DESIGN.md`, section *(B)*).  The two
base cases are proved elsewhere:

* `Dz_Jeps` (`Submission/Work/FTS/StrongEps/Commute.lean`): `D_z (J_ε g) = J_ε (D_z g)` on the
  open quadrant, for `g` of class `C¹` there with continuous `pz g`;
* `Dth_Jeps` (`Submission/Work/FTS/StrongEps/Dth_Jeps.lean`): `D_θ (J_ε g) = J_ε (D_θ g)` on the
  open quadrant, for `g` of class `C¹` there with continuous `pth g`.

Iterating them gives the target `mixed_Jeps`:

`D_z^j D_θ^i (J_ε f) = J_ε (D_z^j D_θ^i f)`   on the open quadrant `Quad = (0,∞) × (0,π/2)`,

for any profile `f` which is `C^n` on `Quad` for every `n`.

## The proof, and why the intermediate profiles are smooth

The outer operator `D_z^j` and the inner operator `D_θ^i` are iterated *separately*:

* (`DthIter_mixed_Jeps`) `D_θ^i (J_ε f) = J_ε (D_θ^i f)` on `Quad`, by induction on `i`.  The
  induction step replaces `D_θ (D_θ^i (J_ε f))` first by `D_θ (J_ε (D_θ^i f))` — legitimate
  because the two functions *agree on the open quadrant*, so their `θ`-slices have the same
  derivative there (`Dth_congrOn`) — and then applies `Dth_Jeps` to the profile `D_θ^i f`.
  This is where the smoothness of `D_θ^i f` is needed: `Dth_Jeps` requires that profile to be
  `C¹` on `Quad` with continuous `θ`-derivative.  The hypothesis `∀ n, ContDiffOn ℝ n f Quad`
  is exactly the statement that `f` is `C^∞` on `Quad` (`contDiffOn_infty`), and `pz`, `pth`,
  `DzIter`, `DthIter` preserve `C^∞`-smoothness on an open set
  (`Work.FTS.LocData.contDiffOn_pz`, …, `contDiffOn_mixed`);
* (`DzIter_Jeps_of_smooth`) `D_z^j (J_ε g) = J_ε (D_z^j g)` on `Quad` for any `g` smooth on
  `Quad`, by induction on `j`, using `Dz_Jeps` and the same congruence argument (`Dz_congrOn`);
* the target follows by composing the congruence `DzIter_congrOn` of the first identity with the
  second one applied to `g = D_θ^i f`.

Everything rests on `[propext, Classical.choice, Quot.sound]` (the imported helper lemmas were
checked to have exactly these axioms).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Commute
import Submission.Work.FTS.StrongEps.Dth_Jeps
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.TransportS.ip4SlotDomFixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1000000

/-! ## `C^∞`-smoothness on the open quadrant, and its closure under the two operators -/

/-- `C^∞`-smoothness of a profile on the open quadrant `Quad = (0,∞) × (0,π/2)`.
(The order `∞` is the genuine smooth order `Work.Stability.smoothOrder`, *not* the analytic
order `⊤` of this Mathlib.) -/
def SmQ (g : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Quad

/-- The hypothesis `∀ n, ContDiffOn ℝ n f Quad` of the target is `C^∞`-smoothness on the open
quadrant (`ContDiffOn` at every *finite* order is the smooth order). -/
theorem smQ_of_forall_nat {g : ℝ → ℝ → ℝ}
    (h : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad) : SmQ g :=
  contDiffOn_infty.mpr h

namespace SmQ

theorem pth {g : ℝ → ℝ → ℝ} (h : SmQ g) : SmQ (Work.Spaces.pth g) :=
  Work.FTS.LocData.contDiffOn_pth isOpen_Quad h

theorem pz {g : ℝ → ℝ → ℝ} (h : SmQ g) : SmQ (Work.Spaces.pz g) :=
  Work.FTS.LocData.contDiffOn_pz isOpen_Quad h

theorem DthIter {g : ℝ → ℝ → ℝ} (h : SmQ g) (i : ℕ) : SmQ (Work.Spaces.DthIter i g) :=
  Work.FTS.LocData.contDiffOn_DthIter isOpen_Quad h i

theorem DzIter {g : ℝ → ℝ → ℝ} (h : SmQ g) (j : ℕ) : SmQ (Work.Spaces.DzIter j g) :=
  Work.FTS.LocData.contDiffOn_DzIter isOpen_Quad h j

/-- `C^∞` on an open set gives `C¹`. -/
theorem one {g : ℝ → ℝ → ℝ} (h : SmQ g) : ContDiffOn ℝ 1 (Function.uncurry g) Quad :=
  h.of_le (by simp)

end SmQ

/-! ## The two inductions -/

/-- **`D_θ^i` commutes with `J_ε`** on the open quadrant. -/
theorem DthIter_mixed_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Jeps ρ ε f)))
      (Function.uncurry (Jeps ρ ε (Work.Spaces.DthIter i f))) Quad := by
  induction i with
  | zero => intro p hp; rfl
  | succ i ih =>
    -- the two functions agree on `Quad`, so `D_θ` of them agrees on `Quad`
    have hcongr := Work.FTS.TransportS.Dth_congrOn isOpen_Quad ih
    -- `D_θ^i f` is smooth on `Quad`, hence `Dth_Jeps` applies to it
    have hsm : SmQ (Work.Spaces.DthIter i f) := (smQ_of_forall_nat hf).DthIter i
    have hpth : SmQ (Work.Spaces.pth (Work.Spaces.DthIter i f)) :=
      Work.FTS.LocData.contDiffOn_pth isOpen_Quad hsm
    intro p hp
    have hz : 0 < p.1 := hp.1
    have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := hp.2
    have h1 : Work.Spaces.Dth (Work.Spaces.DthIter i (Jeps ρ ε f)) p.1 p.2
        = Work.Spaces.Dth (Jeps ρ ε (Work.Spaces.DthIter i f)) p.1 p.2 := hcongr hp
    have h2 : Work.Spaces.Dth (Jeps ρ ε (Work.Spaces.DthIter i f)) p.1 p.2
        = Jeps ρ ε (Work.Spaces.Dth (Work.Spaces.DthIter i f)) p.1 p.2 :=
      Dth_Jeps ρ hρ hε (hsm.one) hpth.continuousOn hz hθ
    change Work.Spaces.DthIter (i + 1) (Jeps ρ ε f) p.1 p.2
        = Jeps ρ ε (Work.Spaces.DthIter (i + 1) f) p.1 p.2
    rw [Work.Spaces.DthIter_succ, h1, h2, Work.Spaces.DthIter_succ]

/-- **`D_z^j` commutes with `J_ε`** on the open quadrant, for any profile `g` smooth there. -/
theorem DzIter_Jeps_of_smooth (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ} (hg : SmQ g) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (Jeps ρ ε g)))
      (Function.uncurry (Jeps ρ ε (Work.Spaces.DzIter j g))) Quad := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
    have hcongr := Work.FTS.TransportS.Dz_congrOn isOpen_Quad ih
    have hsm : SmQ (Work.Spaces.DzIter j g) := hg.DzIter j
    have hpz : SmQ (Work.Spaces.pz (Work.Spaces.DzIter j g)) := hsm.pz
    intro p hp
    have hz : 0 < p.1 := hp.1
    have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := hp.2
    have h1 : Work.Spaces.Dz (Work.Spaces.DzIter j (Jeps ρ ε g)) p.1 p.2
        = Work.Spaces.Dz (Jeps ρ ε (Work.Spaces.DzIter j g)) p.1 p.2 := hcongr hp
    have h2 : Work.Spaces.Dz (Jeps ρ ε (Work.Spaces.DzIter j g)) p.1 p.2
        = Jeps ρ ε (Work.Spaces.Dz (Work.Spaces.DzIter j g)) p.1 p.2 :=
      Dz_Jeps hρ hε hsm.one hpz.continuousOn hz hθ
    change Work.Spaces.DzIter (j + 1) (Jeps ρ ε g) p.1 p.2
        = Jeps ρ ε (Work.Spaces.DzIter (j + 1) g) p.1 p.2
    rw [Work.Spaces.DzIter_succ, h1, h2, Work.Spaces.DzIter_succ]

/-! ## The target -/

/-- **`E1`, iterated form: `D_z^j D_θ^i (J_ε f) = J_ε (D_z^j D_θ^i f)` on the open quadrant**,
for a profile `f` which is `C^n` there for every `n`. -/
theorem mixed_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i (Jeps ρ ε f) z θ = Jeps ρ ε (Work.Spaces.mixed j i f) z θ := by
  have hp : (z, θ) ∈ Quad := ⟨hz, hθ⟩
  -- push the `j` outer `D_z`-derivatives through the equality `D_θ^i (J_ε f) = J_ε (D_θ^i f)`
  have h1 : Set.EqOn
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.DthIter i (Jeps ρ ε f))))
      (Function.uncurry (Work.Spaces.DzIter j (Jeps ρ ε (Work.Spaces.DthIter i f)))) Quad :=
    Work.FTS.TransportS.DzIter_congrOn isOpen_Quad (DthIter_mixed_Jeps ρ hρ hε hf i) j
  -- then commute the `D_z`-iterates with `J_ε` for the smooth profile `D_θ^i f`
  have h2 := DzIter_Jeps_of_smooth ρ hρ hε ((smQ_of_forall_nat hf).DthIter i) j
  exact (h1 hp).trans (h2 hp)

end Work.FTS.StrongEps
