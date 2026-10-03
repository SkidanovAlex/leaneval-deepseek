import Submission.Work.Interfaces.Basic
import Submission.Work.Interfaces.Fatou

/-!
# Parabolic layer contracts for `mandelbrot_boundary_dimh` (design file, lead-owned)

Shishikura, "The Hausdorff dimension of the boundary of the Mandelbrot set" (arXiv math/9201282),
§§4-6 and Appendix, specialised to the cusp: level-0 map `fam α x = e^{2πiα} x + x^2`, `f0 = fam 0`.

Conventions (read before using any Prop):
* `piExp w = exp (2πi w)`, `tau0 w = -1/w` (an involution on `ℂ \ {0}`); the "lift" coordinate `w`
  of a cylinder is a point of `ℂ` and `ℤ` acts by `w ↦ w + 1`.  Horn maps / return maps are always
  handled in LIFTED form: a `T`-equivariant map on a `T`-invariant domain (`IsTEquivariantOn`).  The
  pushed-down map on `ℂ` is `pushdown E` (value `0` at `0`; the end at `∞` is only used in the lift).
* Upper end of a lifted cylinder = `upperEnd = comap im atTop`, lower end = `comap im atBot`.
* Germ class: `f z = z + z^2 + O(z^3)`, i.e. `deriv f 0 = 1` and `deriv (deriv f) 0 = 2`.
  (Shishikura writes "f''(0)=1" but means the coefficient `1` of `z^2`.)  A general germ with
  `f''(0) ≠ 0` is brought to this class by `z ↦ s z`, `s = f''(0)/2` (done in the assembly).
* Shishikura's non-Hausdorff "functions with domains" topology is replaced by explicit
  `(compact L, δ)` closeness: `NearOn f₀ f Df L δ`.
* `rotOf f = log (f' 0) / (2πi)` with the principal `log`, so `-1/2 < Re α ≤ 1/2`.
  Perturbations used: `InF1 α` (`|Im α| < Re α`, i.e. `α ≠ 0`, `|arg α| < π/4`).  Level 0:
  `α = 1/(a₁ - 1/(a₂+β))`; level 1: `α(g) = 1/(a₂+β)`.  The other sign case (4.3.1) is NOT needed.
-/

namespace MandelDim

open Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

/-! ## Coordinates -/

/-- `π(w) = exp(2πiw)`. -/
def piExp (w : ℂ) : ℂ := Complex.exp (2 * Real.pi * I * w)

/-- `τ₀(w) = -1/w`. -/
def tau0 (w : ℂ) : ℂ := -1 / w

/-- Push a `T`-equivariant lifted map down to `ℂ` (the value at `0` is `0`). -/
def pushdown (E : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  if ζ = 0 then 0 else piExp (E (Complex.log ζ / (2 * Real.pi * I)))

def upperEnd : Filter ℂ := Filter.comap Complex.im atTop
def lowerEnd : Filter ℂ := Filter.comap Complex.im atBot

def IsTInvariant (D : Set ℂ) : Prop := ∀ w : ℂ, w ∈ D ↔ w + 1 ∈ D

def IsTEquivariantOn (E : ℂ → ℂ) (D : Set ℂ) : Prop :=
  IsTInvariant D ∧ ∀ w ∈ D, E (w + 1) = E w + 1

/-- Shishikura's `D(η) = {|w - iη| ≤ |η|/4}`. -/
def Dsm (η : ℝ) : Set ℂ := closedBall (I * η) (|η| / 4)
/-- Shishikura's `D'(η) = {|w - iη| ≤ |η|/2}`. -/
def Dbig (η : ℝ) : Set ℂ := closedBall (I * η) (|η| / 2)

/-- The repelling-side sector `Q₀ = {π/3 < arg(w + ξ) < 5π/3}` (principal `arg`). -/
def QLeft (ξ : ℝ) : Set ℂ := {w | Real.pi / 3 < |Complex.arg (w + ξ)|}

/-! ## Germ classes and closeness -/

/-- `f` holomorphic on the open set `D ∋ 0`, `f z = z + z^2 + O(z^3)`. -/
def IsParabolicGerm (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  IsOpen D ∧ (0 : ℂ) ∈ D ∧ DifferentiableOn ℂ f D ∧ f 0 = 0 ∧ deriv f 0 = 1 ∧
    deriv (deriv f) 0 = 2

/-- `f` is holomorphic on the open set `Df ⊇ L` and `δ`-close to `f₀` on `L`. -/
def NearOn (f₀ f : ℂ → ℂ) (Df L : Set ℂ) (δ : ℝ) : Prop :=
  IsOpen Df ∧ L ⊆ Df ∧ DifferentiableOn ℂ f Df ∧ ∀ z ∈ L, ‖f z - f₀ z‖ < δ

/-- rotation number of the fixed point `0`. -/
def rotOf (f : ℂ → ℂ) : ℂ := Complex.log (deriv f 0) / (2 * Real.pi * I)

/-- Shishikura's class `𝓕₁`: `α ≠ 0`, `|arg α| < π/4`. -/
def InF1 (α : ℂ) : Prop := |α.im| < α.re

/-- The parabolic basin of `0` (orbits required to stay in `D`; uniform convergence nearby). -/
def ParabolicBasin (f : ℂ → ℂ) (D : Set ℂ) : Set ℂ :=
  {z | ∃ U ∈ 𝓝 z, (∀ n : ℕ, MapsTo (f^[n]) U D) ∧
    TendstoUniformlyOn (fun n : ℕ => f^[n]) (fun _ => (0 : ℂ)) atTop U}

/-- An immediate parabolic basin: a component of the basin, invariant, `f : B → B` proper. -/
def IsImmediateBasin (f : ℂ → ℂ) (D B : Set ℂ) : Prop :=
  IsOpen B ∧ IsConnected B ∧ B ⊆ ParabolicBasin f D ∧
  (∀ C : Set ℂ, IsPreconnected C → C ⊆ ParabolicBasin f D → (B ∩ C).Nonempty → C ⊆ B) ∧
  MapsTo f B B ∧ B ⊆ f '' B ∧ ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L)

/-- Shishikura's class `𝓕₀`: parabolic germ with an immediate basin containing exactly one
critical point. -/
def InF0 (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  IsParabolicGerm f D ∧ ∃ B, IsImmediateBasin f D B ∧ ∃! c, c ∈ B ∧ deriv f c = 0

/-! ## PARAB0: unperturbed Fatou coordinates and the horn map (§4.1, A.3, Lemma 5.1) -/

/-- The data of §4.1 for a parabolic germ `f₀` on `D₀`.  `φ` is Shishikura's `φ₀` on its MAXIMAL
domain `Dφ`, `Φ` his `Φ₀` on the whole basin, `E = Φ ∘ φ` the lifted horn map `Ẽ_{f₀}` on
`DE = φ⁻¹(basin)`, normalised by `E w - w → 0` at the upper end (this is `E'(0) = 1`, (4.1.5)).
These fields determine `(φ, Φ)` up to one common translation constant. -/
structure ParabData (f₀ : ℂ → ℂ) (D₀ : Set ℂ) where
  ξ₀ : ℝ
  φ : ℂ → ℂ
  Dφ : Set ℂ
  Φ : ℂ → ℂ
  Ωp : Set ℂ
  η₀ : ℝ
  ξ₀_pos : 0 < ξ₀
  Dφ_open : IsOpen Dφ
  Q_sub : QLeft ξ₀ ⊆ Dφ
  /-- maximal domain: every point is a forward translate of the petal ... -/
  exhaust : ∀ w ∈ Dφ, ∃ n : ℕ, w - n ∈ QLeft ξ₀
  left_inv : ∀ w ∈ Dφ, w - 1 ∈ Dφ
  /-- ... and `φ(w+1)` is defined iff `f₀` is defined at `φ w` (4.1.2).  NOTE: `φ w ∉ D₀` is
  allowed (the last point of an orbit need not be in `Dom f₀`; Step 1 needs `φ₀(w̃₀) ∉ Dom`). -/
  succ_iff : ∀ w ∈ Dφ, (w + 1 ∈ Dφ ↔ φ w ∈ D₀)
  φ_holo : DifferentiableOn ℂ φ Dφ
  Q_maps : MapsTo φ (QLeft ξ₀) D₀
  φ_abel : ∀ w ∈ Dφ, w + 1 ∈ Dφ → φ (w + 1) = f₀ (φ w)
  φ_inj : InjOn φ (QLeft ξ₀)
  /-- `φ*₀(w) = w + a log(-w) + b + o(1)` on `Q₀` (branch of `log(-w)` continuous on `Q₀`). -/
  φ_asymp : ∃ a b : ℂ, ∀ ε > 0, ∃ R : ℝ, ∀ w ∈ QLeft ξ₀, R < ‖w‖ →
    ‖tau0 (φ w) - (w + a * Complex.log (-w) + b)‖ < ε
  Φ_holo : DifferentiableOn ℂ Φ (ParabolicBasin f₀ D₀)
  Φ_abel : ∀ z ∈ ParabolicBasin f₀ D₀, Φ (f₀ z) = Φ z + 1
  /-- the attracting petal `Ω₊` of (4.1.1) -/
  Ωp_open : IsOpen Ωp
  Ωp_sub : Ωp ⊆ ParabolicBasin f₀ D₀
  Ωp_maps : MapsTo f₀ Ωp Ωp
  Φ_inj : InjOn Φ Ωp
  /-- (orbits that land exactly on `0` are excluded: `D₀` may be disconnected with `f₀` locally
  constant `= 0` on a component, e.g. `ball 5 1`; then those points are in the basin but never
  enter the petal — machine-checked counterexample in Work/Parab/basinEnters/counterexample.lean) -/
  basin_enter : ∀ z ∈ ParabolicBasin f₀ D₀, (∀ n : ℕ, f₀^[n] z ≠ 0) → ∃ n : ℕ, f₀^[n] z ∈ Ωp
  flower : Ωp ∪ φ '' QLeft ξ₀ ∪ {0} ∈ 𝓝 (0 : ℂ)
  /-- (lead, 09-28, needed by HORN) the petal is connected and simply connected, the iterates
  converge to `0` UNIFORMLY on it ((4.1.1)), and `Φ(Ωp)` contains the tail of every horizontal
  strip (the Fatou coordinate of the seeded library has this image property). -/
  Ωp_conn : IsConnected Ωp
  Ωp_sc : SimplyConnectedSpace Ωp
  Ωp_unif : TendstoUniformlyOn (fun n : ℕ => f₀^[n]) (fun _ => (0 : ℂ)) atTop Ωp
  Φ_image : ∀ b : ℝ, ∃ C : ℝ, ∀ w : ℂ, C < w.re → |w.im| ≤ b → ∃ z ∈ Ωp, Φ z = w
  /-- (4.1.4): the lifted horn map is defined near both ends -/
  ends_sub : ∀ w : ℂ, η₀ < |w.im| → w ∈ Dφ ∧ φ w ∈ ParabolicBasin f₀ D₀
  E_upper : Tendsto (fun w => Φ (φ w) - w) upperEnd (𝓝 0)
  E_lower : ∃ cl : ℂ, Tendsto (fun w => Φ (φ w) - w) lowerEnd (𝓝 cl)
  /-- Lemma 5.1: inverse orbits converging to `0` ↔ points of `Dφ`.
  (The `T`-invariance of `DE` is NOT a field: it is equivalent, via `succ_iff` and the invariance
  of the basin, to `φ (Dφ) ⊆ D₀`, which fails for bounded `D₀` — see
  `Work.Horn.DE_T_of_phi_maps_to_D0` and `NOTES_SESSION14.md` §2.) -/
  invOrbit : ∀ z : ℕ → ℂ, (∀ j, 1 ≤ j → z j ∈ D₀) → (∀ j, f₀ (z (j + 1)) = z j) →
    Tendsto z atTop (𝓝 0) → (∃ j, z j ≠ 0) →
    ∃ w ∈ Dφ, (∀ j : ℕ, w - j ∈ Dφ ∧ φ (w - j) = z j) ∧
      ((∀ j, 1 ≤ j → deriv f₀ (z j) ≠ 0) → deriv φ w ≠ 0)

  /-- (lead, 09-29) basin orbits never land exactly on the fixed point `0`.  This is the
  non-degeneracy hypothesis of `ParabStatement`, carried by the data so that every consumer of `d`
  (PERT's crux, the horn map on `DE`) has it.  It is NOT implied by the other fields when `f₀` is
  locally constant on a component of `D₀` (two-disc germ, see `basin_enter`). -/
  orbit_avoid : ∀ z ∈ ParabolicBasin f₀ D₀, ∀ n : ℕ, f₀^[n] z ≠ 0

namespace ParabData
variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀)
/-- lifted horn map `Ẽ_{f₀} = Φ₀ ∘ φ₀` -/
def E : ℂ → ℂ := fun w => d.Φ (d.φ w)
/-- its domain `φ₀⁻¹(basin)` (it is `T`-invariant) -/
def DE : Set ℂ := {w | w ∈ d.Dφ ∧ d.φ w ∈ ParabolicBasin f₀ D₀}
end ParabData

/-- **Lemma 5.4 basin clause** (lead, 10-03; formerly the `ParabData.horn_basin` FIELD).  For every
`𝓕₀`-situation the pushed-down horn map `g = pushdown d.E` on `D_g = {0} ∪ π (Bu ∪ Bl)` has a
`g`-invariant component `B'` of its parabolic basin on which `g` is proper, simply connected and
containing a critical point.  It is a THEOREM about any `d` (`Work.Horn.horn_basin_thm`, route in
`Submission/Work/Horn/HB/DESIGN.md`), not a field: it follows from the other fields + `InF0` via the
finite local monodromy of `g` over its critical value. -/
def HornBasinClause {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) : Prop :=
  InF0 f₀ D₀ → ∀ (B : Set ℂ), IsImmediateBasin f₀ D₀ B → ∀ (Bu Bl : Set ℂ),
    Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (d.η₀ + 1)) →
    Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (d.η₀ + 1))) →
    ∃ B' : Set ℂ,
      (∃ z ∈ ParabolicBasin (pushdown (fun w => d.Φ (d.φ w)))
          (insert 0 (piExp '' (Bu ∪ Bl))),
        B' = connectedComponentIn (ParabolicBasin (pushdown (fun w => d.Φ (d.φ w)))
          (insert 0 (piExp '' (Bu ∪ Bl)))) z) ∧
      Set.MapsTo (pushdown (fun w => d.Φ (d.φ w))) B' B' ∧
      (∀ L : Set ℂ, L ⊆ B' → IsCompact L →
        IsCompact (B' ∩ (pushdown (fun w => d.Φ (d.φ w))) ⁻¹' L)) ∧
      SimplyConnectedSpace B' ∧
      ∃ z ∈ B', deriv (pushdown (fun w => d.Φ (d.φ w))) z = 0

/-- PARAB0 (area): every parabolic germ carries §4.1 data. -/
def ParabStatement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ : Set ℂ), IsParabolicGerm f₀ D₀ →
    (∀ z ∈ ParabolicBasin f₀ D₀, ∀ n : ℕ, (f₀^[n]) z ≠ 0) → Nonempty (ParabData f₀ D₀)

/-! ## PERT: perturbed Fatou coordinates and the return map (A.1, A.4, (4.2.1)-(4.2.5)) -/

/-- The output of §4.2 for one perturbation `f` (holomorphic on `Df`), at scale `η`, with
closeness `δ` on the compact sets `K ⊆ DE₀` (horn map) and `K' ⊆ Dφ₀` (coordinate).
`φ` is `φ_f` on a domain `Dφ`, `R` the lifted return map `R̃_f` (so `pushdown R = R_f`). -/
structure PertData {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (f : ℂ → ℂ) (Df : Set ℂ)
    (η y₁ : ℝ) (K K' : Set ℂ) (δ : ℝ) where
  φ : ℂ → ℂ
  Dφ : Set ℂ
  R : ℂ → ℂ
  DR : Set ℂ
  Dφ_open : IsOpen Dφ
  φ_holo : DifferentiableOn ℂ φ Dφ
  /-- functional equation; `φ w ∈ Df` whenever `w + 1` is still in the domain -/
  φ_abel : ∀ w ∈ Dφ, w + 1 ∈ Dφ → φ w ∈ Df ∧ φ (w + 1) = f (φ w)
  /-- (4.2.5), both ends, plus `φ*_f = id + O(η/40)` (needed for the factor-2 IFS balls) -/
  D_sub : Dsm η ∪ Dsm (-η) ⊆ Dφ
  /-- (lead, 09-28, REPEL's §4.2 domain information; (4.2.1): `Dom φ_f ⊇ 𝒬_f`, which contains the
  unit-width vertical strip at every height `≥ y₁` for `f` close enough to `f₀`).  Used so that the
  level-0 target lift (real part in `[-1/2,1/2]`, height `≈ η + log|s|/2π`) lies in `Dφ`. -/
  Dφ_strip : ∀ w : ℂ, y₁ ≤ |w.im| → |w.re| ≤ 1 → w ∈ Dφ
  φ_inj_up : InjOn φ (Dsm η)
  φ_inj_dn : InjOn φ (Dsm (-η))
  φ_star_close : ∀ w ∈ Dsm η ∪ Dsm (-η), ‖tau0 (φ w) - w‖ ≤ |η| / 40
  φ_star_deriv : ∀ w ∈ Dsm η ∪ Dsm (-η),
    1 / 2 < ‖deriv (fun u => tau0 (φ u)) w‖ ∧ ‖deriv (fun u => tau0 (φ u)) w‖ < 2
  /-- (4.2.4), first half: `φ_f → φ₀` on compacts of the maximal domain -/
  K'_sub : K' ⊆ Dφ
  φ_close : ∀ w ∈ K', ‖φ w - d.φ w‖ < δ
  /-- the lifted return map -/
  DR_open : IsOpen DR
  R_equiv : IsTEquivariantOn R DR
  R_holo : DifferentiableOn ℂ R DR
  DR_sub : K ∪ {w | y₁ ≤ |w.im|} ⊆ DR
  /-- (4.2.4), second half: `R̃_f + 1/α → Ẽ_{f₀}` on `K` and uniformly near both ends -/
  R_close : ∀ w ∈ K ∪ {w | y₁ ≤ |w.im|}, ‖R w + 1 / rotOf f - d.E w‖ < δ
  /-- (4.2.2): `R_f'(0) = exp(-2πi/α)` exactly -/
  R_upper : Tendsto (fun w => R w - w + 1 / rotOf f) upperEnd (𝓝 0)
  /-- (4.2.3) with the restriction (A.4.5') `|R w + 1/α - w| < 1/(8|α|)` on `DR` (the paper's
  `1/(2α)` does not force `n ≥ 1`); the points before the last stay in `Df`. -/
  orbit : ∀ w ∈ Dφ, ∀ w' ∈ Dφ, ∀ m : ℕ, 1 ≤ m → (∀ j < m, R^[j] w ∈ DR) →
    piExp (R^[m] w) = piExp w' →
    |Complex.arg (w' + 1 / (2 * rotOf f) - w)| < 2 * Real.pi / 3 →
    ∃ n : ℕ, 1 ≤ n ∧ f^[n] (φ w) = φ w' ∧ ∀ i < n, f^[i] (φ w) ∈ Df

/-- PERT (area; may assume the FATOU Prop): for every parabolic germ with its §4.1 data, every
large `η`, every pair of compacts and every `δ`, all perturbations in a `(L, δ₀)`-neighbourhood
with `f 0 = 0` and `α(f) ∈ 𝓕₁` carry the §4.2 data. -/
def PertStatement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : ParabData f₀ D₀), IsParabolicGerm f₀ D₀ →
  ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, η₁ ≤ η →
  ∀ y₁ : ℝ, d.η₀ < y₁ →
  ∀ K K' : Set ℂ, IsCompact K → K ⊆ d.DE → IsCompact K' → K' ⊆ d.Dφ → ∀ δ : ℝ, 0 < δ →
  ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (f : ℂ → ℂ) (Df : Set ℂ), NearOn f₀ f Df L δ₀ → f 0 = 0 → InF1 (rotOf f) →
      Nonempty (PertData d f Df η y₁ K K' δ)

/-! ## HORN: global structure of the horn map (Prop 5.3, Lemma 5.4) -/

/-- The conclusions of Prop 5.3 (lifted) and Lemma 5.4 for `f₀ ∈ 𝓕₀`. `Bu, Bl` are the
components of `φ₀⁻¹(B)` (`B` the immediate basin) containing the upper/lower half planes;
`v` is a lift of the unique critical value. `gdom = {0} ∪ π(Bu ∪ Bl)` is the domain of the
pushed-down horn map `g₀ = pushdown E` (the point `∞` is not used). -/
structure HornData {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) where
  Bu : Set ℂ
  Bl : Set ℂ
  η : ℝ
  v : ℂ
  Bu_open : IsOpen Bu
  Bl_open : IsOpen Bl
  Bu_conn : IsConnected Bu
  Bl_conn : IsConnected Bl
  Bu_sc : SimplyConnectedSpace Bu
  Bl_sc : SimplyConnectedSpace Bl
  Bu_T : IsTInvariant Bu
  Bl_T : IsTInvariant Bl
  disj : Disjoint Bu Bl
  sub : Bu ∪ Bl ⊆ d.DE
  upper : {w : ℂ | η < w.im} ⊆ Bu
  lower : {w : ℂ | w.im < -η} ⊆ Bl
  /-- the only critical values are `v + ℤ` -/
  crit : ∀ w ∈ Bu ∪ Bl, deriv d.E w = 0 → ∃ k : ℤ, d.E w = v + k
  cov_u : IsCoveringMapOn (fun x : Bu => d.E x) {y | ∀ k : ℤ, y ≠ v + k}
  cov_l : IsCoveringMapOn (fun x : Bl => d.E x) {y | ∀ k : ℤ, y ≠ v + k}
  surj_u : ∀ y : ℂ, ∃ w ∈ Bu, d.E w = y
  surj_l : ∀ y : ℂ, ∃ w ∈ Bl, d.E w = y
  /-- infinite degree (of the pushed-down map on each of `B^u`, `B^ℓ`) -/
  inf_u : ∀ y : ℂ, (piExp '' {w | w ∈ Bu ∧ d.E w = y}).Infinite
  inf_l : ∀ y : ℂ, (piExp '' {w | w ∈ Bl ∧ d.E w = y}).Infinite
  /-- Lemma 5.4: the pushed-down horn map is again in `𝓕₀` after the scaling `ζ ↦ s ζ` -/
  g_holo : DifferentiableOn ℂ (pushdown d.E) (insert 0 (piExp '' (Bu ∪ Bl)))
  g_deriv : deriv (pushdown d.E) 0 = 1
  g_second : deriv (deriv (pushdown d.E)) 0 ≠ 0
  g_F0 : InF0 (fun ζ => (deriv (deriv (pushdown d.E)) 0 / 2) *
      pushdown d.E (ζ / (deriv (deriv (pushdown d.E)) 0 / 2)))
    ((fun ζ => (deriv (deriv (pushdown d.E)) 0 / 2) * ζ) '' insert 0 (piExp '' (Bu ∪ Bl)))
  /-- the lower-end constant of the lifted horn map has positive imaginary part (for `f₀ = z+z²`,
  `cl = 2πi`; in general `2πi·(iterative residue)`).  Proof: at the upper end `E ≈ w`, so if the
  critical value class were not in `Bu` the global inverse branch `H` of `pushdown E` on the
  BOUNDED set `π(Bu) ∪ {0}` would have `|H'(0)| = 1`, contradicting strict Schwarz (`E` is not
  injective on `Bu`, `inf_u`); hence the critical value is not in `Bl`, and strict Schwarz at the
  lower end (inverse `≈ ζ - cl`) gives `0 < Im cl`.  Needed by L62 (end choice for every `β`). -/
  cl_im_pos : ∀ cl : ℂ, Tendsto (fun w => d.E w - w) lowerEnd (𝓝 cl) → 0 < cl.im
  crit_orbit : (∀ n : ℕ, (pushdown d.E)^[n] (piExp v) ∈ piExp '' (Bu ∪ Bl)) ∧
    Tendsto (fun n : ℕ => (pushdown d.E)^[n] (piExp v)) atTop (𝓝 0)

/-- HORN (area): Prop 5.3 + Lemma 5.4 for the abstract class `𝓕₀` (applied to `f₀` AND to `ǧ₀`). -/
def HornStatement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ : Set ℂ), InF0 f₀ D₀ → ∀ d : ParabData f₀ D₀, Nonempty (HornData d)

/-! ## L61, L62: the two inverse-orbit lemmas of §6 -/

/-- Lemma 6.1 for `g₀ = pushdown Ẽ_{f₀}`: two disjoint non-critical inverse orbits of a point
`w₀ ∉ Dom g₀`, converging to `0`. -/
def L61Statement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ : Set ℂ), InF0 f₀ D₀ → ∀ (d : ParabData f₀ D₀) (hd : HornData d),
  ∀ w₀ : ℂ, w₀ ≠ 0 → w₀ ∉ insert 0 (piExp '' (hd.Bu ∪ hd.Bl)) →
  ∃ wa wb : ℕ → ℂ, wa 0 = w₀ ∧ wb 0 = w₀ ∧
    (∀ j, wa (j + 1) ∈ piExp '' (hd.Bu ∪ hd.Bl) ∧ pushdown d.E (wa (j + 1)) = wa j ∧
      deriv (pushdown d.E) (wa (j + 1)) ≠ 0) ∧
    (∀ j, wb (j + 1) ∈ piExp '' (hd.Bu ∪ hd.Bl) ∧ pushdown d.E (wb (j + 1)) = wb j ∧
      deriv (pushdown d.E) (wb (j + 1)) ≠ 0) ∧
    Tendsto wa atTop (𝓝 0) ∧ Tendsto wb atTop (𝓝 0) ∧
    ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → wa i ≠ wb j

/-- Lemma 6.2 (lifted `ℂ/ℤ` model) for `g₀ ∈ 𝓕₀` with horn map `h₀ = Ẽ_{g₀}` (`d.E`):
for every lifted `R` close to `h₀` on `K` and near both ends and every `β` with `|Im β| ≤ b`,
`ĥ = R - β` (β in one period `0 ≤ Re β ≤ 1`: the paper's β ∈ ℂ/ℤ; for other β use
T-equivariance of `R`) has a backward chain of discs `W j` marching to one end (sign `s`), with uniform
derivative bounds. `W 0` is a ball of any radius `ρ ≤ ρ₀` about `ζa` or `ζb`. -/
def L62Statement : Prop :=
  ∀ (g₀ : ℂ → ℂ) (D : Set ℂ), InF0 g₀ D → ∀ (d : ParabData g₀ D) (_hd : HornData d),
  ∀ b : ℝ, 0 < b → ∀ ζa ζb : ℂ, ζa ∉ d.DE → ζb ∉ d.DE → (∀ k : ℤ, ζa ≠ ζb + k) →
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
  ∃ K : Set ℂ, IsCompact K ∧ K ⊆ d.DE ∧ ∃ y₁ δ C₀ C₁ C₁' : ℝ, d.η₀ < y₁ ∧ 0 < δ ∧ 0 < C₁ ∧
  ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR → IsTEquivariantOn R DR → DifferentiableOn ℂ R DR →
    K ∪ {w | y₁ ≤ |w.im|} ⊆ DR → (∀ w ∈ K ∪ {w | y₁ ≤ |w.im|}, ‖R w - d.E w‖ < δ) →
  ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b →
  ∃ (W : ℕ → Set ℂ) (s : ℝ), (s = 1 ∨ s = -1) ∧
    (W 0 = ball ζa ρ ∨ W 0 = ball ζb ρ) ∧
    (∀ j, IsOpen (W j) ∧ IsConnected (W j)) ∧
    (∀ j, W (j + 1) ⊆ DR ∧ InjOn (fun w => R w - β) (W (j + 1)) ∧
      (fun w => R w - β) '' W (j + 1) = W j) ∧
    (∀ i j, i ≠ j → Disjoint (piExp '' W i) (piExp '' W j)) ∧
    (∀ M : ℝ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ w ∈ W j, M < s * w.im) ∧
    (∀ j, Bornology.IsBounded (W j) ∧ Metric.diam (W j) < 1 / 2) ∧
    (∀ j, ∃ u ∈ W j, ∃ u' ∈ W (j + 1), ‖u - u'‖ < C₀) ∧
    (∀ j, ∀ w ∈ W j, C₁ < ‖deriv ((fun u => R u - β)^[j]) w‖ ∧
      ‖deriv ((fun u => R u - β)^[j]) w‖ < C₁')

/-! ## F0FACTS: the level-0 germ -/

def f0 (x : ℂ) : ℂ := x + x ^ 2

/-- `f₀ = x + x²` is in `𝓕₀` (on `ℂ`), and Step 0 holds with an inverse orbit of `0` avoiding the
critical point `-1/2` entirely (so Shishikura's Step 5 is not needed: `k = 0`, `ν = 1`). -/
def F0FactsStatement : Prop :=
  InF0 f0 univ ∧ ∃ z : ℕ → ℂ, z 0 = 0 ∧ (∀ j, f0 (z (j + 1)) = z j) ∧
    (∀ j, 1 ≤ j → z j ≠ 0) ∧ Tendsto z atTop (𝓝 0) ∧ ∀ j, z j ≠ -1 / 2

/-- REPEL/ASSEMBLY (area): Steps 0-6 of §6 from the area Props. `FatouStatement` enters only
through `PertStatement`. -/
def RepelStatement : Prop :=
  ParabStatement → PertStatement → HornStatement → L61Statement → L62Statement →
    F0FactsStatement → DynStatement

end

end MandelDim
