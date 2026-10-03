import Mathlib
import Submission.Work.Repel.V10.chain_v9_setup
import Submission.Work.Repel.box_piExp_surj
import Submission.Work.Repel.chain_preimage_mem
import Submission.Work.Repel.walk_of_sub
import Submission.Work.Repel.walk_of_germ1
import Submission.Work.Repel.uniform_iterate_of_orbit
import Submission.Work.Repel.exists_piExp_lift

/-!
# `Work.Repel.chain_v9_chase` : the §6 composite for `chain_returns_v9`

Shishikura's §6 composite for a cell `q = (j, k, n)` (chain index `j`, `Re`-translate `k`, box
index `n`):

  `z --(φ₀|box)⁻¹--> w₀ --s·π--> ζ --(φ₁|Dsm)⁻¹--> u ∈ W j + k --ĥ^j--> u' ∈ W 0 --π⁻¹--> w₁ --φ₀--> z'`

with `ĥ = R - β` and `π w₁ = φ₁ u' / s`.  This file defines the four maps

* `V10.uOf ζ` — the level-1 source `(φ₁|Dsm(sgn η₁))⁻¹ ζ`,
* `V10.bOf n ζ` — the box lift of `ζ` in the half-open fundamental domain `B n`,
* `V10.wOf u'` — the target lift of `φ₁ u'/s` inside `ball wt₀ ρ₀`,
* `V10.wOfCell q w` — the level-0 target attached to the source `w`,

together with their pointwise specifications.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

namespace V10

variable (V : V10)

/-- The level-1 disc selected by the marching direction `sgn`: `Dsm η₁` for `sgn = 1` and
`Dsm (-η₁)` for `sgn = -1`.  This is the region where `φ₁ = P₁.φ` is injective and satisfies the
`φ_star_close` asymptotics, and it contains every counted fibre `W j + k`. -/
def Sm1 : Set ℂ := if V.sgn = 1 then Dsm V.η₁ else Dsm (-V.η₁)

theorem Sm1_injOn : Set.InjOn V.P₁.φ V.Sm1 := by
  rw [Sm1]
  split
  · exact V.P₁.φ_inj_up
  · exact V.P₁.φ_inj_dn

theorem Sm1_sub_Dφ : V.Sm1 ⊆ V.P₁.Dφ := by
  rw [Sm1]
  intro z hz
  split at hz
  · exact V.P₁.D_sub (Or.inl hz)
  · exact V.P₁.D_sub (Or.inr hz)

theorem phi_bounds_of_mem_Sm1 {u : ℂ} (hu : u ∈ V.Sm1) :
    40 / (51 * V.η₁) ≤ ‖V.P₁.φ u‖ ∧ ‖V.P₁.φ u‖ ≤ 40 / (29 * V.η₁) := by
  rw [Sm1] at hu
  split at hu
  · exact phi_norm_bounds V.P₁ V.hη₁pos (Or.inl hu)
  · exact phi_norm_bounds V.P₁ V.hη₁pos (Or.inr hu)

/-- The level-1 source of a point of the level-1 plane: the inverse of `φ₁` on the disc `Sm1`. -/
def uOf (ζ : ℂ) : ℂ := Function.invFunOn V.P₁.φ V.Sm1 ζ

theorem uOf_spec {ζ : ℂ} (hζ : ζ ∈ V.P₁.φ '' V.Sm1) :
    V.uOf ζ ∈ V.Sm1 ∧ V.P₁.φ (V.uOf ζ) = ζ :=
  ⟨Function.invFunOn_mem hζ, Function.invFunOn_eq hζ⟩

theorem uOf_unique {ζ u : ℂ} (hu : u ∈ V.Sm1) (h : V.P₁.φ u = ζ) : V.uOf ζ = u :=
  V.Sm1_injOn (V.uOf_spec ⟨u, hu, h⟩).1 hu (by rw [V.uOf_spec ⟨u, hu, h⟩ |>.2, h])

/-- The half-open full-period box of Shishikura §6 Step 3: `Re` window `[n, n+1)` (a fundamental
domain of `π`) and imaginary part in `(η + log(1/2)/2π, η + log(3/2)/2π)`.  Every point of `B n`
has modulus in `(2e^{-2πη}/3, 2e^{-2πη})`, and `π : B n →` that annulus is a bijection. -/
def B (n : ℤ) : Set ℂ :=
  {w : ℂ | (n : ℝ) ≤ w.re ∧ w.re < (n : ℝ) + 1 ∧
    V.η + Real.log (1 / 2) / (2 * Real.pi) < w.im ∧
    w.im < V.η + Real.log (3 / 2) / (2 * Real.pi)}

theorem B_injOn (n : ℤ) : Set.InjOn MandelDim.piExp (V.B n) := by
  intro a ha b hb hab
  obtain ⟨ha1, ha2, -, -⟩ := ha
  obtain ⟨hb1, hb2, -, -⟩ := hb
  obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hab
  have hre : (k : ℝ) = a.re - b.re := by
    have h := congrArg Complex.re hk
    simp at h
    linarith [h]
  have hk0 : k = 0 := by
    have h1 : (k : ℝ) < 1 := by linarith [hre, ha2, hb1]
    have h2 : (-1 : ℝ) < (k : ℝ) := by linarith [hre, ha1, hb2]
    have h1z : k < 1 := by exact_mod_cast h1
    have h2z : (-1 : ℤ) < k := by exact_mod_cast h2
    omega
  rw [hk0] at hk
  norm_num at hk
  exact hk

/-- The box lift of a nonzero `ζ` in the fundamental domain `B n`. -/
def bOf (n : ℤ) (ζ : ℂ) : ℂ := Function.invFunOn MandelDim.piExp (V.B n) ζ

theorem bOf_spec {n : ℤ} {ζ : ℂ}
    (hζ : ζ ∈ MandelDim.piExp '' (V.B n)) :
    V.bOf n ζ ∈ V.B n ∧ MandelDim.piExp (V.bOf n ζ) = ζ :=
  ⟨Function.invFunOn_mem hζ, Function.invFunOn_eq hζ⟩

theorem bOf_unique {n : ℤ} {ζ w : ℂ} (hw : w ∈ V.B n) (h : MandelDim.piExp w = ζ) :
    V.bOf n ζ = w :=
  V.B_injOn n (V.bOf_spec ⟨w, hw, h⟩).1 hw (by rw [V.bOf_spec ⟨w, hw, h⟩ |>.2, h])

/-- The modulus of `π` on the box `B n` is in `(2e^{-2πη}/3, 2e^{-2πη})`. -/
theorem exp_bounds_of_mem_B {n : ℤ} {w : ℂ} (hw : w ∈ V.B n) :
    2 * Real.exp (-(2 * Real.pi * V.η)) / 3 < ‖MandelDim.piExp w‖ ∧
      ‖MandelDim.piExp w‖ < 2 * Real.exp (-(2 * Real.pi * V.η)) := by
  obtain ⟨-, -, h1, h2⟩ := hw
  have hnorm : ‖MandelDim.piExp w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    rw [MandelDim.piExp, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hexp : Real.exp (-(2 * Real.pi * w.im))
      = Real.exp (-(2 * Real.pi * V.η)) * Real.exp (-(2 * Real.pi * (w.im - V.η))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 < Real.exp (-(2 * Real.pi * V.η)) := Real.exp_pos _
  have hlog12 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  have hlog23 : Real.log ((2 : ℝ) / 3) = Real.log 2 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have hlog32 : Real.log ((3 : ℝ) / 2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  have hlow : -(Real.log 2) / (2 * Real.pi) < w.im - V.η := by
    rw [hlog12] at h1
    linarith
  have hhigh : w.im - V.η < Real.log ((3 : ℝ) / 2) / (2 * Real.pi) := by linarith
  have hlow' : -(Real.log 2) < 2 * Real.pi * (w.im - V.η) := by
    have h := (div_lt_iff₀ (show (0 : ℝ) < 2 * Real.pi by positivity)).mp hlow
    linarith [h]
  have hhigh' : 2 * Real.pi * (w.im - V.η) < Real.log 3 - Real.log 2 := by
    have h := (lt_div_iff₀ (show (0 : ℝ) < 2 * Real.pi by positivity)).mp hhigh
    rw [hlog32] at h
    linarith [h]
  have ha : Real.exp (-(2 * Real.pi * (w.im - V.η))) < 2 := by
    have h2' : Real.exp (-(2 * Real.pi * (w.im - V.η))) < Real.exp (Real.log 2) := by
      rw [Real.exp_lt_exp]
      nlinarith [hlow']
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h2'
  have hb : (2 : ℝ) / 3 < Real.exp (-(2 * Real.pi * (w.im - V.η))) := by
    have h3 : Real.exp (Real.log ((2 : ℝ) / 3)) < Real.exp (-(2 * Real.pi * (w.im - V.η))) := by
      rw [Real.exp_lt_exp, hlog23]
      nlinarith [hhigh']
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < (2 : ℝ) / 3)] at h3
  rw [hnorm, hexp]
  constructor
  · nlinarith [hb, hpos]
  · nlinarith [ha, hpos]

/-- The target lift: the unique point of `ball wt₀ ρ₀` whose `π`-image is `φ₁ u'/s`. -/
def wOf (V : V10) (u' : ℂ) : ℂ :=
  @dite ℂ (u' ∈ V.W 0) (Classical.propDecidable _)
    (fun h => Classical.choose (V.htgt u' h)) (fun _ => V.wt₀)

theorem wOf_spec {u' : ℂ} (hu' : u' ∈ V.W 0) :
    V.wOf u' ∈ Metric.ball V.wt₀ V.ρ₀ ∧ MandelDim.piExp (V.wOf u') = V.P₁.φ u' / V.s := by
  rw [wOf, dif_pos hu']
  exact Classical.choose_spec (V.htgt u' hu')

theorem wOf_unique {u' w : ℂ} (hu' : u' ∈ V.W 0) (hw : w ∈ Metric.ball V.wt₀ V.ρ₀)
    (h : MandelDim.piExp w = V.P₁.φ u' / V.s) : V.wOf u' = w :=
  piExp_injOn_ball_lift V.hρ₀le (V.wOf_spec hu').1 hw (by rw [(V.wOf_spec hu').2, h])

theorem wOf_differentiableOn : DifferentiableOn ℂ V.wOf (V.W 0) := by
  have hWo : IsOpen (V.W 0) := by rw [V.hbase]; exact Metric.isOpen_ball
  have hφ : DifferentiableOn ℂ V.P₁.φ (V.W 0) :=
    V.P₁.φ_holo.mono (fun z hz => V.hsub₁ (by rwa [V.hbase] at hz))
  obtain ⟨W, hWd, hWspec, -⟩ :=
    exists_piExp_lift (V := V.W 0) (f := fun u' => V.P₁.φ u' / V.s)
      (a := V.wt₀) (ρ₀ := V.ρ₀) hWo (hφ.div_const V.s) V.hρ₀le
      (fun v hv => by
        obtain ⟨w, hw, hπ⟩ := V.htgt v hv
        exact ⟨w, hw, by rw [hπ]⟩)
  refine hWd.congr (fun u' hu' => ?_)
  exact V.wOf_unique hu' (hWspec u' hu').1 (by rw [(hWspec u' hu').2])

/-- The source region of the cell `q = (j,k,n)`: the level-0 box `B n` cut down to the points
whose level-1 image `s·π w` lies in the fibre `φ₁ '' (W j + k)`. -/
def Src (q : ℕ × ℤ × ℤ) : Set ℂ :=
  {w : ℂ | w ∈ V.B q.2.2 ∧
    V.s * MandelDim.piExp w ∈ V.P₁.φ '' ((fun x : ℂ => x + ((q.2.1 : ℤ) : ℂ)) '' V.W q.1)}

/-- The level-1 source of a point of the source region. -/
def uOfSrc (q : ℕ × ℤ × ℤ) (w : ℂ) : ℂ := V.uOf (V.s * MandelDim.piExp w)

theorem uOfSrc_spec {q : ℕ × ℤ × ℤ} {w : ℂ}
    (hSm : (fun x : ℂ => x + ((q.2.1 : ℤ) : ℂ)) '' V.W q.1 ⊆ V.Sm1) (hw : w ∈ V.Src q) :
    V.uOfSrc q w ∈ V.Sm1 ∧ V.s * MandelDim.piExp w = V.P₁.φ (V.uOfSrc q w) := by
  rw [uOfSrc]
  exact ⟨(V.uOf_spec (Set.image_mono hSm hw.2)).1,
    (V.uOf_spec (Set.image_mono hSm hw.2)).2.symm⟩

theorem uOfSrc_mem_fibre {q : ℕ × ℤ × ℤ} {w : ℂ}
    (hSm : (fun x : ℂ => x + ((q.2.1 : ℤ) : ℂ)) '' V.W q.1 ⊆ V.Sm1) (hw : w ∈ V.Src q) :
    V.uOfSrc q w ∈ (fun x : ℂ => x + ((q.2.1 : ℤ) : ℂ)) '' V.W q.1 := by
  obtain ⟨u, hu, hπ⟩ := hw.2
  rw [uOfSrc]
  exact (V.uOf_unique (hSm hu) hπ) ▸ hu

/-- The level-0 target attached to a source point of the cell `q`: lift `φ₁ u'/s` and iterate the
chain.  The map `z ↦ φ₀ (wOfCell q ((φ₀|box)⁻¹ z))` is Shishikura's §6 composite. -/
def wOfCell (q : ℕ × ℤ × ℤ) (w : ℂ) : ℂ :=
  V.wOf ((fun x : ℂ => V.R x - V.β)^[q.1] (V.uOfSrc q w) - ((q.2.1 : ℤ) : ℂ))

theorem wOfCell_spec {q : ℕ × ℤ × ℤ} {w : ℂ}
    (hW0 : (fun x : ℂ => V.R x - V.β)^[q.1] (V.uOfSrc q w) - ((q.2.1 : ℤ) : ℂ) ∈ V.W 0) :
    V.wOfCell q w ∈ Metric.ball V.wt₀ V.ρ₀ ∧
      MandelDim.piExp (V.wOfCell q w) =
        V.P₁.φ ((fun x : ℂ => V.R x - V.β)^[q.1] (V.uOfSrc q w) - ((q.2.1 : ℤ) : ℂ)) / V.s := by
  rw [wOfCell]
  exact V.wOf_spec hW0

end V10

end

end Work.Repel
