import Mathlib
import Submission.Work.OddCurve.LowSlope.radonProfile_data_semicircle
import Submission.Work.OddRadon.AbelInversion
import Submission.Work.OddRadon.contDiffOn_radonProfile

/-!
# The two Radon data of the odd low-slope step, and their junction (`LowSlope/Datum`)

The paper's Step 3 constructs the remaining part of the profile from the *spherical-Radon data* of
the body.  For a body of revolution with radial function `ρ` (in the `u = cos α` variable,
`f (ρ u · u) = ρ u √(1-u²)`) the two data are

    φ_ρ(c) = 𝓡(w₁² ρ^{d+1})(ξ)  =  `radonPhi n ρ c`,
    ψ_ρ(c) = 𝓡(w₁ ρ^d)(ξ)      =  `radonPsi n ρ c`,

where `ξ` is the normal with `ξ₀ = c`.  The *ball* has `ρ ≡ 1`, hence
`φ_ball(c) = radonProfile (2n+1) (·)² c = (2n+2)|B^{2n-1}|·ballInertiaConst n·c²` on `(0,1]`
(`ballPhiData`, `ballPhiData_eq`) and `ψ_ball ≡ 0` (by the parity `radonProfile_odd`).

## The junction

Step 3 keeps the anchor's data on the cap and replaces them by the ball's below the junction
slope `s = 3/4`, i.e. above `c = 4/5`: the glued data are

    `gluedPhi n φa c = if c < 4/5 then φa c else ballPhiData n c`,
    `gluedPsi ψa c   = if c < 4/5 then ψa c else 0`.

They are `C^∞` on `(0,1)` as soon as `φa` (resp. `ψa`) is `C^∞` there and agrees with the ball's
data (resp. with `0`) on a *neighbourhood* of `c = 4/5` — which is exactly what the two junction
lemmas `anchorPhiData_eq_ballData` / `anchorPsiData_eq_zero` supply, on the slope range
`(a,b) ⊆ (1-3τ, 1-2τ)` where the bump vanishes.

The point ``4/5` is `1 - 2τ`; it is the right junction because the agreement interval of the
anchor with the ball is `c ∈ (cos arctan b, cos arctan a) ⊇ (0.7847, 0.8153) ∋ 4/5` for
`(a,b) = (0.71, 0.79)`, and because `s = 3/4` is the slope at which `c = 4/5`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The ball's first Radon datum `radonProfile (2n+1) (·)²`: the transform of the second moment
`w ↦ w₁²` of the unit ball. -/
def ballPhiData (n : ℕ) (c : ℝ) : ℝ :=
  Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2) c

/-- The ball's second Radon datum: `0`, by the oddness of `u ↦ u`. -/
def ballPsiData (_ : ℝ) : ℝ := 0

/-- The first Radon datum of the body of revolution with radial function `ρ`:
`𝓡 (w₁² ρ^{d+1})`. -/
def radonPhi (n : ℕ) (ρ : ℝ → ℝ) (c : ℝ) : ℝ :=
  Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) c

/-- The second Radon datum of the body of revolution with radial function `ρ`:
`𝓡 (w₁ ρ^d)`. -/
def radonPsi (n : ℕ) (ρ : ℝ → ℝ) (c : ℝ) : ℝ :=
  Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u * ρ u ^ (2 * n + 1)) c

/-- The **glued first datum**: the anchor's on the cap `|c| < 4/5`, the ball's below.

The `|c|` (rather than `c`) is essential: the datum of a body of revolution is an *even* function
of `c` (`radonProfile_neg`), and the inversion `radonProfile_radonInverse` is stated for even
data.  With the cap written as `c < 4/5` the glued function would fail to be even on the half
`c < -4/5`, and would therefore not be the datum of any body. -/
def gluedPhi (n : ℕ) (φa : ℝ → ℝ) (c : ℝ) : ℝ :=
  if |c| < 4 / 5 then φa c else ballPhiData n c

/-- The **glued second datum**: the anchor's on the cap `|c| < 4/5`, `0` below. -/
def gluedPsi (ψa : ℝ → ℝ) (c : ℝ) : ℝ :=
  if |c| < 4 / 5 then ψa c else 0

@[simp] lemma gluedPhi_of_abs_lt {n : ℕ} {φa : ℝ → ℝ} {c : ℝ} (hc : |c| < 4 / 5) :
    gluedPhi n φa c = φa c := if_pos hc

@[simp] lemma gluedPhi_of_abs_ge {n : ℕ} {φa : ℝ → ℝ} {c : ℝ} (hc : 4 / 5 ≤ |c|) :
    gluedPhi n φa c = ballPhiData n c := if_neg (not_lt.mpr hc)

@[simp] lemma gluedPsi_of_abs_lt {ψa : ℝ → ℝ} {c : ℝ} (hc : |c| < 4 / 5) :
    gluedPsi ψa c = ψa c := if_pos hc

@[simp] lemma gluedPsi_of_abs_ge {ψa : ℝ → ℝ} {c : ℝ} (hc : 4 / 5 ≤ |c|) :
    gluedPsi ψa c = 0 := if_neg (not_lt.mpr hc)

/-- On the positive axis the cap is the interval `(0,4/5)`. -/
lemma gluedPhi_of_lt {n : ℕ} {φa : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hc' : c < 4 / 5) :
    gluedPhi n φa c = φa c := gluedPhi_of_abs_lt (by rwa [abs_of_nonneg hc])

lemma gluedPhi_of_ge {n : ℕ} {φa : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hc' : 4 / 5 ≤ c) :
    gluedPhi n φa c = ballPhiData n c := gluedPhi_of_abs_ge (by rwa [abs_of_nonneg hc])

lemma gluedPsi_of_lt {ψa : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hc' : c < 4 / 5) :
    gluedPsi ψa c = ψa c := gluedPsi_of_abs_lt (by rwa [abs_of_nonneg hc])

lemma gluedPsi_of_ge {ψa : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hc' : 4 / 5 ≤ c) :
    gluedPsi ψa c = 0 := gluedPsi_of_abs_ge (by rwa [abs_of_nonneg hc])

/-- Every Radon datum is an even function of `c` (`radonProfile_neg`). -/
lemma ballPhiData_neg (n : ℕ) (c : ℝ) : ballPhiData n (-c) = ballPhiData n c :=
  Work.OddRadon.radonProfile_neg (2 * n + 1) (fun u : ℝ => u ^ 2) c

lemma radonPhi_neg (n : ℕ) (ρ : ℝ → ℝ) (c : ℝ) : radonPhi n ρ (-c) = radonPhi n ρ c :=
  Work.OddRadon.radonProfile_neg (2 * n + 1) (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) c

lemma radonPsi_neg (n : ℕ) (ρ : ℝ → ℝ) (c : ℝ) : radonPsi n ρ (-c) = radonPsi n ρ c :=
  Work.OddRadon.radonProfile_neg (2 * n + 1) (fun u : ℝ => u * ρ u ^ (2 * n + 1)) c

/-- The glued datum is even, as any Radon datum must be. -/
lemma gluedPhi_even {n : ℕ} {φa : ℝ → ℝ} (hφ : ∀ c, φa (-c) = φa c) (c : ℝ) :
    gluedPhi n φa (-c) = gluedPhi n φa c := by
  unfold gluedPhi
  rw [abs_neg, hφ, ballPhiData_neg]

/-- The glued second datum is even. -/
lemma gluedPsi_even {ψa : ℝ → ℝ} (hψ : ∀ c, ψa (-c) = ψa c) (c : ℝ) :
    gluedPsi ψa (-c) = gluedPsi ψa c := by
  unfold gluedPsi
  rw [abs_neg, hψ]

/-- The ball's first datum in closed form: `(2n+2)|B^{2n-1}|·ballInertiaConst n·c²` on `(0,1]`. -/
lemma ballPhiData_eq (n : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ballPhiData n c = (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) * ballInertiaConst n * c ^ 2 :=
  radonProfile_data_semicircle n hn hc hc1

/-- The ball's first datum is `C^∞` on `(0,1)`. -/
theorem contDiffOn_ballPhiData (n : ℕ) (hn : 1 ≤ n) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ballPhiData n) (Set.Ioo (0 : ℝ) 1) := by
  have hpoly : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => (2 * (n : ℝ) + 2) * ballVol (2 * n - 1) * ballInertiaConst n * c ^ 2)
      (Set.Ioo (0 : ℝ) 1) := by fun_prop
  exact hpoly.congr (fun c hc => ballPhiData_eq n hn hc.1 (le_of_lt hc.2))

/-- The glued first datum is `C^∞` on `(0,1)`, provided the anchor's datum is and agrees with the
ball's on a neighbourhood of the junction `c = 4/5`. -/
theorem contDiffOn_gluedPhi (n : ℕ) (hn : 1 ≤ n) {φa : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φa (Set.Ioo (0 : ℝ) 1))
    (hagree : ∀ c ∈ Set.Ioo ((4 : ℝ) / 5 - δ) ((4 : ℝ) / 5 + δ), φa c = ballPhiData n c) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gluedPhi n φa) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx
  rcases lt_trichotomy x (4 / 5) with hlt | heq | hgt
  · -- below the junction the glued datum is the anchor's
    refine (hsm x hx).congr_of_eventuallyEq ?_ (gluedPhi_of_lt hx.1.le hlt)
    have hnb : Set.Ioo (0 : ℝ) (4 / 5) ∈ 𝓝[Set.Ioo (0 : ℝ) 1] x :=
      mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds isOpen_Ioo ⟨hx.1, hlt⟩)
    filter_upwards [hnb] with c hc using gluedPhi_of_lt hc.1.le hc.2
  · -- at the junction the two pieces agree, so use the anchor's datum
    refine (hsm x hx).congr_of_eventuallyEq ?_ ?_
    · have hnb : Set.Ioo ((4 : ℝ) / 5 - δ) ((4 : ℝ) / 5 + δ) ∈ 𝓝[Set.Ioo (0 : ℝ) 1] x :=
        mem_nhdsWithin_of_mem_nhds
          (IsOpen.mem_nhds isOpen_Ioo ⟨by rw [heq]; linarith, by rw [heq]; linarith⟩)
      filter_upwards [hnb, self_mem_nhdsWithin] with c hc hc01
      rcases lt_or_ge c (4 / 5) with hc' | hc'
      · exact gluedPhi_of_lt hc01.1.le hc'
      · rw [gluedPhi_of_ge hc01.1.le hc']; exact (hagree c hc).symm
    · rw [heq, gluedPhi_of_ge (by norm_num : (0 : ℝ) ≤ 4 / 5) le_rfl,
        ← hagree ((4 : ℝ) / 5) ⟨by linarith, by linarith⟩]
  · -- above the junction the glued datum is the ball's
    refine ((contDiffOn_ballPhiData n hn) x hx).congr_of_eventuallyEq ?_
      (gluedPhi_of_ge hx.1.le (le_of_lt hgt))
    have hnb : Set.Ioo ((4 : ℝ) / 5) 1 ∈ 𝓝[Set.Ioo (0 : ℝ) 1] x :=
      mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds isOpen_Ioo ⟨hgt, hx.2⟩)
    filter_upwards [hnb] with c hc using
      gluedPhi_of_ge (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 4 / 5) hc.1)) (le_of_lt hc.1)

/-- The glued second datum is `C^∞` on `(0,1)`, provided the anchor's datum is and vanishes on a
neighbourhood of the junction `c = 4/5`. -/
theorem contDiffOn_gluedPsi {ψa : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψa (Set.Ioo (0 : ℝ) 1))
    (hagree : ∀ c ∈ Set.Ioo ((4 : ℝ) / 5 - δ) ((4 : ℝ) / 5 + δ), ψa c = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gluedPsi ψa) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx
  rcases lt_trichotomy x (4 / 5) with hlt | heq | hgt
  · refine (hsm x hx).congr_of_eventuallyEq ?_ (gluedPsi_of_lt hx.1.le hlt)
    have hnb : Set.Ioo (0 : ℝ) (4 / 5) ∈ 𝓝[Set.Ioo (0 : ℝ) 1] x :=
      mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds isOpen_Ioo ⟨hx.1, hlt⟩)
    filter_upwards [hnb] with c hc using gluedPsi_of_lt hc.1.le hc.2
  · refine (hsm x hx).congr_of_eventuallyEq ?_ ?_
    · have hnb : Set.Ioo ((4 : ℝ) / 5 - δ) ((4 : ℝ) / 5 + δ) ∈ 𝓝[Set.Ioo (0 : ℝ) 1] x :=
        mem_nhdsWithin_of_mem_nhds
          (IsOpen.mem_nhds isOpen_Ioo ⟨by rw [heq]; linarith, by rw [heq]; linarith⟩)
      filter_upwards [hnb, self_mem_nhdsWithin] with c hc hc01
      rcases lt_or_ge c (4 / 5) with hc' | hc'
      · exact gluedPsi_of_lt hc01.1.le hc'
      · rw [gluedPsi_of_ge hc01.1.le hc']; exact (hagree c hc).symm
    · rw [heq, gluedPsi_of_ge (by norm_num : (0 : ℝ) ≤ 4 / 5) le_rfl,
        ← hagree ((4 : ℝ) / 5) ⟨by linarith, by linarith⟩]
  · refine (contDiffWithinAt_const (x := x) (s := Set.Ioo (0 : ℝ) 1) (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      (gluedPsi_of_ge hx.1.le (le_of_lt hgt))
    have hnb : Set.Ioo ((4 : ℝ) / 5) 1 ∈ 𝓝[Set.Ioo (0 : ℝ) 1] x :=
      mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds isOpen_Ioo ⟨hgt, hx.2⟩)
    filter_upwards [hnb] with c hc using
      gluedPsi_of_ge (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 4 / 5) hc.1)) (le_of_lt hc.1)

/-- The first datum `radonPhi n ρ` is `C^∞` on `(0,1)` when `ρ` is `C^∞` on `(-1,1)` and the
profile function `u ↦ u²ρ(u)^{2n+2}` extends continuously to `[-1,1]`. -/
theorem contDiffOn_radonPhi (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hcont : ContinuousOn (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) (Set.Icc (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radonPhi n ρ) (Set.Ioo (0 : ℝ) 1) := by
  have hγ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) (Set.Ioo (-1 : ℝ) 1) :=
    (contDiffOn_id.pow 2).mul (hρ.pow (2 * n + 2))
  exact Work.OddRadon.contDiffOn_radonProfile n hn hγ hcont

/-- The second datum `radonPsi n ρ` is `C^∞` on `(0,1)` when `ρ` is `C^∞` on `(-1,1)` and the
profile function `u ↦ u ρ(u)^{2n+1}` extends continuously to `[-1,1]`. -/
theorem contDiffOn_radonPsi (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hcont : ContinuousOn (fun u : ℝ => u * ρ u ^ (2 * n + 1)) (Set.Icc (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radonPsi n ρ) (Set.Ioo (0 : ℝ) 1) := by
  have hγ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => u * ρ u ^ (2 * n + 1)) (Set.Ioo (-1 : ℝ) 1) :=
    contDiffOn_id.mul (hρ.pow (2 * n + 1))
  exact Work.OddRadon.contDiffOn_radonProfile n hn hγ hcont

/-- **Locality of `radonInverse`**: the value at `u` depends only on the datum on `(0,b)` for any
`b > u`.  (Used to transfer the agreement `φ_new = φ_a` on `(0,4/5)` to the reconstructed radial
function on the same range.) -/
theorem radonInverse_congr_of_eqOn (n : ℕ) {F G : ℝ → ℝ} {u b : ℝ} (hu : 0 < u) (hub : u < b)
    (h : ∀ c ∈ Set.Ioo (0 : ℝ) b, F c = G c) :
    Work.OddRadon.radonInverse n F u = Work.OddRadon.radonInverse n G u := by
  have hEq : Set.EqOn
      (fun c : ℝ => (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F c)
      (fun c : ℝ => (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * G c)
      (Set.Ioo (0 : ℝ) b) := by
    intro c hc
    simp only [h c hc]
  have hred := Work.OddRadon.abelReduceIter_congr_open (s := Set.Ioo (0 : ℝ) b) isOpen_Ioo
    (n - 1) ((n : ℝ) - 3 / 2) hEq
  exact Work.OddRadon.abelInvert_congr_of_eqOn hu hub hred

/-- On the cap the glued datum is the anchor's, so its inverse is the anchor's too. -/
theorem radonInverse_gluedPhi_eq_of_lt (n : ℕ) {φa : ℝ → ℝ} {u : ℝ} (hu : 0 < u)
    (hu' : u < 4 / 5) :
    Work.OddRadon.radonInverse n (gluedPhi n φa) u = Work.OddRadon.radonInverse n φa u :=
  radonInverse_congr_of_eqOn (b := 4 / 5) n hu (by linarith)
    (fun c hc => gluedPhi_of_lt hc.1.le hc.2)

/-- On the cap the glued second datum is the anchor's, so its inverse is the anchor's too. -/
theorem radonInverse_gluedPsi_eq_of_lt (n : ℕ) {ψa : ℝ → ℝ} {u : ℝ} (hu : 0 < u)
    (hu' : u < 4 / 5) :
    Work.OddRadon.radonInverse n (gluedPsi ψa) u = Work.OddRadon.radonInverse n ψa u :=
  radonInverse_congr_of_eqOn (b := 4 / 5) n hu (by linarith)
    (fun c hc => gluedPsi_of_lt hc.1.le hc.2)

end

end Work.OddCurve.LowSlope
