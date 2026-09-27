import Mathlib
import Submission.Mostow.Interfaces

/-!
# Toolkit for `QIProp`

Definitions and elementary (fully proved) lemmas used by the area-C3 development.

* `POBasic`, `HypIsoData` bundle the two hypothesis `Prop`s `POActionProp`, `HypIsometryProp`
  into structures with readable field names.
* `mink` is the Minkowski form of the hyperboloid model; `hdist_eq_arcosh_mink`.
* `geo` is the explicit geodesic between two points of `ℍⁿ` in the chart model.
* `lev`, `wc`, `yc` are the Busemann level, the ξ^⊥-coordinate and the normalised
  ("flat") coordinate of a point at a boundary point `ξ`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- Bundled form of `POActionProp n`. -/
structure POBasic (n : ℕ) : Prop where
  center_mem : ∀ A : O1 n, A ∈ Subgroup.center (O1 n) ↔ A = 1 ∨ A = -1
  coe_smul : ∀ (A : O1 n) (u : E n), (A : PO n 1) • u = actO A u
  coe_bd : ∀ (A : O1 n) (ξ : E n), ξ ∈ Sph n → bd (A : PO n 1) ξ = bdO A ξ
  one_smul : ∀ u : E n, (1 : PO n 1) • u = u
  mul_smul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u)
  faithful : ∀ g : PO n 1, (∀ u : E n, g • u = u) → g = 1
  continuous_smul : Continuous (fun p : PO n 1 × E n => p.1 • p.2)
  bd_mem : ∀ (g : PO n 1) (ξ : E n), ξ ∈ Sph n → bd g ξ ∈ Sph n
  bd_one : ∀ ξ ∈ Sph n, bd (1 : PO n 1) ξ = ξ
  bd_mul : ∀ (g h : PO n 1) (ξ : E n), ξ ∈ Sph n → bd (g * h) ξ = bd g (bd h ξ)
  bd_continuous : ∀ g : PO n 1, ContinuousOn (bd g) (Sph n)
  bd_measurable : ∀ g : PO n 1, Measurable (bd g)

theorem POBasic.ofProp {n : ℕ} (h : POActionProp n) : POBasic n :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Bundled form of `HypIsometryProp n`. -/
structure HypIsoData (n : ℕ) : Prop where
  nonneg : ∀ u v : E n, 0 ≤ hdist u v
  symm : ∀ u v : E n, hdist u v = hdist v u
  eq_zero : ∀ u v : E n, hdist u v = 0 ↔ u = v
  triangle : ∀ u v w : E n, hdist u w ≤ hdist u v + hdist v w
  continuous : Continuous (fun p : E n × E n => hdist p.1 p.2)
  ball_compact : ∀ (u : E n) (r : ℝ), IsCompact {v | hdist u v ≤ r}
  isom_smul : ∀ (g : PO n 1) (u v : E n), hdist (g • u) (g • v) = hdist u v
  surj_isom : ∀ F : E n → E n, (∀ u v, hdist (F u) (F v) = hdist u v) →
    ∃ g : PO n 1, ∀ u, F u = g • u
  contDiff_smul : ∀ g : PO n 1, ContDiff ℝ 1 (fun u : E n => g • u)
  metric_smul : ∀ (g : PO n 1) (u v : E n),
    gH (g • u) (fderiv ℝ (fun w : E n => g • w) u v) = gH u v
  jac_smul : ∀ (g : PO n 1) (u : E n), hjac (fun w : E n => g • w) u = 1
  measurePreserving_smul : ∀ g : PO n 1, MeasurePreserving (fun u : E n => g • u) (volH n) (volH n)
  busemann_cocycle : ∀ (g : PO n 1) (ξ u : E n), ξ ∈ Sph n →
    busemann (bd g ξ) (g • u) = busemann ξ u + busemann (bd g ξ) (g • (0 : E n))

theorem HypIsoData.ofProp {n : ℕ} (h : HypIsometryProp n) : HypIsoData n :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## The Minkowski form and `hdist` -/

/-- The Minkowski bilinear form of the hyperboloid model. -/
def mink (x y : Fin n ⊕ Fin 1 → ℝ) : ℝ :=
  (∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i)) - x (Sum.inr 0) * y (Sum.inr 0)

/-- `hdist` is the Minkowski pairing of the corresponding hyperboloid points. -/
theorem hdist_eq_arcosh_mink (u v : E n) :
    hdist u v = Real.arcosh (-(mink (hlift u) (hlift v))) := by
  simp only [hdist, mink, hlift, tpart, PiLp.inner_apply, Real.inner_apply,
    Sum.elim_inl, Sum.elim_inr]
  ring

/-! ## The explicit geodesic in the chart model -/

/-- Linear interpolation vector in the hyperboloid, normalised to lie on the hyperboloid. -/
noncomputable def geoVec (u v : E n) (s : ℝ) : Fin n ⊕ Fin 1 → ℝ :=
  if u = v then hlift u
  else
    (Real.sinh (hdist u v))⁻¹ •
      (Real.sinh ((1 - s) * hdist u v) • hlift u + Real.sinh (s * hdist u v) • hlift v)

/-- The point of `ℍⁿ` at parameter `s` on the geodesic from `u` to `v`. -/
noncomputable def geo (u v : E n) (s : ℝ) : E n :=
  WithLp.toLp 2 (fun i => geoVec u v s (Sum.inl i))

/-! ## Busemann level, ξ^⊥-coordinate, normalised flat coordinate -/

/-- `lev ξ u = tpart u - ⟪u,ξ⟫ = exp (busemann ξ u)`: the level of the horosphere at `ξ`
through `u`. -/
noncomputable def lev (ξ u : E n) : ℝ := tpart u - inner ℝ u ξ

/-- The component of `u` in `ξ^⊥`. -/
noncomputable def wc (ξ u : E n) : E n := u - inner ℝ u ξ • ξ

/-- The normalised flat coordinate of `u` at `ξ`. -/
noncomputable def yc (ξ u : E n) : E n := (lev ξ u)⁻¹ • wc ξ u

theorem lev_pos (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) : 0 < lev ξ u := by
  have h1 : ‖ξ‖ = 1 := by
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have h2 : inner ℝ u ξ ≤ ‖u‖ * ‖ξ‖ := real_inner_le_norm u ξ
  have h3 : tpart u = Real.sqrt (1 + ‖u‖ ^ 2) := rfl
  have h4 : Real.sqrt (1 + ‖u‖ ^ 2) > ‖u‖ := by
    have : (1:ℝ) + ‖u‖^2 > ‖u‖^2 := by linarith
    calc Real.sqrt (1 + ‖u‖^2) > Real.sqrt (‖u‖^2) := Real.sqrt_lt_sqrt (by positivity) this
      _ = ‖u‖ := Real.sqrt_sq (norm_nonneg u)
  rw [lev, h3]
  nlinarith [h1, h2, h4, norm_nonneg u]

theorem lev_eq_exp {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    lev ξ u = Real.exp (busemann ξ u) := by
  have h : 0 < lev ξ u := lev_pos ξ hξ u
  simp only [busemann]
  exact (Real.exp_log h).symm

theorem lev_smul (hI : HypIsoData n) (hA : POBasic n) (ξ : E n) (hξ : ξ ∈ Sph n) (g : PO n 1) (u : E n) :
    lev (bd g ξ) (g • u) = lev ξ u * lev (bd g ξ) (g • (0 : E n)) := by
  have h := hI.busemann_cocycle g ξ u hξ
  have h2 : bd g ξ ∈ Sph n := hA.bd_mem g ξ hξ
  rw [lev_eq_exp hξ u, lev_eq_exp h2 (g • u), lev_eq_exp h2 (g • (0 : E n)), h, Real.exp_add]

theorem lev_smul_self (hI : HypIsoData n) (hA : POBasic n) (ξ : E n) (hξ : ξ ∈ Sph n) (g : PO n 1) (u : E n)
    (hg : bd g ξ = ξ) : lev ξ (g • u) = lev ξ u * lev ξ (g • (0 : E n)) := by
  have := lev_smul (n := n) hI hA ξ hξ g u
  rwa [hg] at this

/-! ## The flat distance on a horosphere -/

/-- The flat (Euclidean) distance on the horosphere of `ξ` between the horospheres through
`u` and `v`: at the *same* level this is the intrinsic flat distance. -/
noncomputable def flatD (ξ u v : E n) : ℝ := ‖yc ξ u - yc ξ v‖

section Model

variable (ξ y : E n)

/-- The null vector `n_ξ = (ξ,1)` corresponding to the boundary point `ξ`. -/
def nvec (ξ : E n) : Fin n ⊕ Fin 1 → ℝ := Sum.elim (fun i => ξ i) (fun _ => (1 : ℝ))

/-- The "opposite" null vector `(-ξ,1)`, with `⟨n_ξ, n_ξ'⟩ = -2`. -/
def nvec' (ξ : E n) : Fin n ⊕ Fin 1 → ℝ := Sum.elim (fun i => -(ξ i)) (fun _ => (1 : ℝ))

/-- The vector `(w,0)`, i.e. `w` placed in the spacelike part. -/
def wvec (w : E n) : Fin n ⊕ Fin 1 → ℝ := Sum.elim (fun i => w i) (fun _ => (0 : ℝ))

/-- The effective matrix of an element of `PO n 1`: the unique representative preserving the
upper sheet. -/
noncomputable def emat (g : PO n 1) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  tsign (rep g) • mat (rep g)

/-- The point of the level-`1` horosphere of `ξ` with flat coordinate `y`. -/
noncomputable def horoPt (ξ y : E n) : E n := (‖y‖ ^ 2 / 2) • ξ + y

/-- The point at level `D` with flat coordinate `y` at `ξ`. -/
noncomputable def hptOf (ξ y : E n) (D : ℝ) : E n :=
  ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2) • ξ + D • y

end Model


/-! ## Cusp vocabulary -/

/-- The boundary fixed points of parabolic elements of `Γ`, i.e. the cusps of `Γ`. -/
def parFixSet (Γ : Subgroup (PO n 1)) : Set (E n) :=
  {ξ | ξ ∈ Sph n ∧ ∃ γ : Γ, IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ}

/-- The set of elements of `Γ` stabilising the boundary point `ξ`. -/
def cuspStabSet (Γ : Subgroup (PO n 1)) (ξ : E n) : Set (PO n 1) :=
  {g | g ∈ Γ ∧ bd g ξ = ξ}

/-- The flat action on `ξ^⊥` of an element fixing `ξ` and preserving the levels: the
normalised flat coordinate of `γ • horoPt ξ y`. -/
noncomputable def flatAct (ξ : E n) (γ : PO n 1) (y : E n) : E n := yc ξ (γ • horoPt ξ y)

/-- `u` lies in the horoball of `ξ` at level `t` (i.e. `busemann ξ u < t`). -/
def inHoro (ξ : E n) (t : ℝ) (u : E n) : Prop := lev ξ u < Real.exp t

end Work.Mostow
