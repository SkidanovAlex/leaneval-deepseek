import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.DzAmgm.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The derivative of the identity function. -/
theorem deriv_self (z : ℝ) : deriv (fun y : ℝ => y) z = 1 := by
  rw [show (fun y : ℝ => y) = id from rfl, deriv_id]

/-! ## The operator `Q = z² ∂_z²` and the local calculus of the open quadrant

The target identity is stated on the open quadrant `Q0 = (0,∞) × (0,π/2)`, so everything below
is *local*: all differentiation happens at interior points of the quadrant, where the functions
at hand are `C^n` for every `n` (this is what `SmoothOpen` provides).  In particular the
commutation of `D_z` with the iterates of `D_θ` is obtained from the pointwise Clairaut identity
`Work.Spaces.Dz_Dth_comm`, which only needs `C²`: the lemma `Work.Spaces.DzDthIterCommOn` of the
library is stated with the hypothesis `ContDiffOn ℝ ⊤`, and in this Mathlib `⊤` is *analyticity*,
which `SmoothOpen` does not provide. -/

/-- The operator `Q = z² ∂_z²` acting on functions of `(z,θ)`: `Qop g z θ = z² ∂_z² g (z,θ)`. -/
def Qop (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 g z θ

variable {g : ℝ → ℝ → ℝ}

/-! ### Slices of a function that is smooth on the open quadrant -/

theorem contDiffOn_slice_z_nat {G : ℝ → ℝ → ℝ} {N : ℕ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ N (Function.uncurry G) (s ×ˢ t)) {θ : ℝ} (hθ : θ ∈ t) :
    ContDiffOn ℝ N (fun z => G z θ) s := by
  have h1 : ContDiffOn ℝ (N : WithTop ℕ∞) (fun z : ℝ => (z, θ)) s :=
    (contDiffOn_id : ContDiffOn ℝ (N : WithTop ℕ∞) (fun z : ℝ => z) s).prodMk
      (contDiffOn_const (c := θ))
  exact (hG.comp h1 (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

theorem contDiffOn_slice_θ_nat {G : ℝ → ℝ → ℝ} {N : ℕ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ N (Function.uncurry G) (s ×ˢ t)) {z : ℝ} (hz : z ∈ s) :
    ContDiffOn ℝ N (fun θ => G z θ) t := by
  have h1 : ContDiffOn ℝ (N : WithTop ℕ∞) (fun θ : ℝ => (z, θ)) t :=
    (contDiffOn_const (c := z)).prodMk
      (contDiffOn_id : ContDiffOn ℝ (N : WithTop ℕ∞) (fun θ : ℝ => θ) t)
  exact (hG.comp h1 (fun θ hθ => ⟨hz, hθ⟩)).congr (fun θ _ => rfl)

/-- The `z`-slice of a function smooth on the open quadrant is `C^N` on `(0,∞)`. -/
theorem slice_z_contDiffOn (hg : SmoothOpen g) (N : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ N (fun z => g z θ) (Set.Ioi 0) :=
  contDiffOn_slice_z_nat (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2)) (hg.forall N) hθ

/-- The `θ`-slice of a function smooth on the open quadrant is `C^N` on `(0,π/2)`. -/
theorem slice_θ_contDiffOn (hg : SmoothOpen g) (N : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ N (fun θ => g z θ) (Set.Ioo 0 (π / 2)) :=
  contDiffOn_slice_θ_nat (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2)) (hg.forall N) hz

/-- The `z`-slice of a function smooth on the open quadrant is differentiable at every `z > 0`. -/
theorem differentiableAt_slice_z_of (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : DifferentiableAt ℝ (fun z' => g z' θ) z :=
  ((slice_z_contDiffOn hg 1 hθ).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- The `θ`-slice of a function smooth on the open quadrant is differentiable at every
interior angle. -/
theorem differentiableAt_slice_θ_of (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : DifferentiableAt ℝ (fun θ' => g z θ') θ :=
  ((slice_θ_contDiffOn hg 1 hz).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)

/-- The `∂_z`-derivative of the `z`-slice of a function smooth on the open quadrant is again
differentiable at every `z > 0`. -/
theorem differentiableAt_deriv_slice_z_of (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : DifferentiableAt ℝ (deriv (fun z' => g z' θ)) z :=
  (((slice_z_contDiffOn hg 2 hθ).deriv_of_isOpen (m := 1) isOpen_Ioi
      (by norm_num)).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- A function smooth on the open quadrant is `C²` at every point of the quadrant. -/
theorem contDiffAt_two_of_mem (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ) :=
  (hg.contDiffAt (isOpen_Q0.mem_nhds (mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))).of_le
    (by simp [Work.Stability.smoothOrder])

/-! ### Locality of `D_z`, `D_θ` and their iterates on the open quadrant -/

theorem Q0_Dz_congr {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz A)) (Function.uncurry (Work.Spaces.Dz B)) Q0 := by
  intro p hp
  have hz : Work.Spaces.pz A p.1 p.2 = Work.Spaces.pz B p.1 p.2 :=
    Work.Spaces.pz_congr_of_isOpen isOpen_Q0 h hp
  show p.1 * Work.Spaces.pz A p.1 p.2 = p.1 * Work.Spaces.pz B p.1 p.2
  rw [hz]

theorem Q0_Dth_congr {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth A)) (Function.uncurry (Work.Spaces.Dth B)) Q0 := by
  intro p hp
  have hθ : Work.Spaces.pth A p.1 p.2 = Work.Spaces.pth B p.1 p.2 :=
    Work.Spaces.pth_congr_of_isOpen isOpen_Q0 h hp
  show Real.sin (2 * p.2) * Work.Spaces.pth A p.1 p.2
      = Real.sin (2 * p.2) * Work.Spaces.pth B p.1 p.2
  rw [hθ]

theorem Q0_DzIter_congr {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter k A))
      (Function.uncurry (Work.Spaces.DzIter k B)) Q0 := by
  induction k with
  | zero => exact h
  | succ k ih => simpa only [Work.Spaces.DzIter_succ] using Q0_Dz_congr ih

theorem Q0_DthIter_congr {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter k A))
      (Function.uncurry (Work.Spaces.DthIter k B)) Q0 := by
  induction k with
  | zero => exact h
  | succ k ih => simpa only [Work.Spaces.DthIter_succ] using Q0_Dth_congr ih

/-! ### `∂_z` and `∂_θ` of a difference -/

theorem Q0_pz_sub {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun z' => A z' θ) z)
    (hB : DifferentiableAt ℝ (fun z' => B z' θ) z) :
    Work.Spaces.pz (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.pz A z θ - Work.Spaces.pz B z θ := by
  have hfun : (fun z' : ℝ => A z' θ - B z' θ)
      = (fun z' => A z' θ) - (fun z' => B z' θ) := by
    funext x; rfl
  show deriv (fun z' => A z' θ - B z' θ) z
      = deriv (fun z' => A z' θ) z - deriv (fun z' => B z' θ) z
  rw [hfun, deriv_sub hA hB]

theorem Q0_pth_sub {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun θ' => A z θ') θ)
    (hB : DifferentiableAt ℝ (fun θ' => B z θ') θ) :
    Work.Spaces.pth (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.pth A z θ - Work.Spaces.pth B z θ := by
  have hfun : (fun θ' : ℝ => A z θ' - B z θ')
      = (fun θ' => A z θ') - (fun θ' => B z θ') := by
    funext x; rfl
  show deriv (fun θ' => A z θ' - B z θ') θ
      = deriv (fun θ' => A z θ') θ - deriv (fun θ' => B z θ') θ
  rw [hfun, deriv_sub hA hB]

/-! ### `Q = D_z² - D_z` on the open quadrant -/

/-- **`z²∂_z² = D_z(D_z - 1)` on the open quadrant.**  For `g` smooth on `Q0` and
`(z,θ) ∈ Q0`, `z²∂_z² g = D_z² g - D_z g`.  The one-variable content is
`z²u'' = z(zu')' - zu'`, i.e. `(zu')' = u' + zu''` by the product rule. -/
theorem Qop_eq_Dz2_sub_Dz (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Qop g z θ = Work.Spaces.DzIter 2 g z θ - Work.Spaces.DzIter 1 g z θ := by
  have hderiv : DifferentiableAt ℝ (deriv (fun z' => g z' θ)) z :=
    differentiableAt_deriv_slice_z_of hg hz hθ
  have hpz2 : Work.Spaces.pzIter 2 g z θ = deriv (deriv (fun z' => g z' θ)) z := by
    rw [Work.Spaces.pzIter_eq_iteratedDeriv, iteratedDeriv_succ, iteratedDeriv_one]
  have hfun : (fun y => Work.Spaces.DzIter 1 g y θ)
      = fun y => y * deriv (fun z' => g z' θ) y := by
    funext y
    rfl
  have hdm : deriv (fun y => y * deriv (fun z' => g z' θ) y) z
      = deriv (fun z' => g z' θ) z + z * deriv (deriv (fun z' => g z' θ)) z := by
    have hmul := deriv_mul (c := fun y : ℝ => y) (d := deriv (fun z' => g z' θ))
      differentiableAt_id hderiv
    have hfun2 : ((fun y : ℝ => y) * deriv (fun z' => g z' θ))
        = fun y => y * deriv (fun z' => g z' θ) y := by
      funext x; rfl
    rw [hfun2] at hmul
    rw [deriv_self] at hmul
    simpa only [one_mul] using hmul
  show z ^ 2 * Work.Spaces.pzIter 2 g z θ
      = Work.Spaces.DzIter 2 g z θ - Work.Spaces.DzIter 1 g z θ
  rw [hpz2]
  show z ^ 2 * deriv (deriv (fun z' => g z' θ)) z
      = z * deriv (fun y => Work.Spaces.DzIter 1 g y θ) z
        - z * deriv (fun z' => g z' θ) z
  rw [hfun, hdm]
  ring

/-! ### `Q` commutes with `D_z` -/

/-- On the open quadrant, `Q = z²∂_z²` commutes with `D_z = z∂_z`. -/
theorem Qop_Dz_eq (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Qop (Work.Spaces.Dz g) z θ = Work.Spaces.Dz (Qop g) z θ := by
  have hmem : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hEqOn : Set.EqOn (Function.uncurry (Qop g))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter 2 g z θ
        - Work.Spaces.DzIter 1 g z θ)) Q0 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_Q0.mp hp
    exact Qop_eq_Dz2_sub_Dz hg h1 ⟨h2, h3⟩
  have hpzcongr : Work.Spaces.pz (Qop g) z θ
      = Work.Spaces.pz (fun z θ => Work.Spaces.DzIter 2 g z θ
          - Work.Spaces.DzIter 1 g z θ) z θ :=
    Work.Spaces.pz_congr_of_isOpen isOpen_Q0 hEqOn hmem
  have hsub : Work.Spaces.pz (fun z θ => Work.Spaces.DzIter 2 g z θ
        - Work.Spaces.DzIter 1 g z θ) z θ
      = Work.Spaces.pz (Work.Spaces.DzIter 2 g) z θ
        - Work.Spaces.pz (Work.Spaces.DzIter 1 g) z θ :=
    Q0_pz_sub (differentiableAt_slice_z_of (hg.DzIter 2) hz hθ)
      (differentiableAt_slice_z_of (hg.DzIter 1) hz hθ)
  have hdec : Qop (Work.Spaces.Dz g) z θ
      = Work.Spaces.DzIter 3 g z θ - Work.Spaces.DzIter 2 g z θ := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
      using Qop_eq_Dz2_sub_Dz (hg.Dz) hz hθ
  have hrhs : Work.Spaces.Dz (Qop g) z θ
      = Work.Spaces.DzIter 3 g z θ - Work.Spaces.DzIter 2 g z θ := by
    show z * Work.Spaces.pz (Qop g) z θ
        = Work.Spaces.DzIter 3 g z θ - Work.Spaces.DzIter 2 g z θ
    rw [hpzcongr, hsub]
    show z * (Work.Spaces.pz (Work.Spaces.DzIter 2 g) z θ
          - Work.Spaces.pz (Work.Spaces.DzIter 1 g) z θ)
        = z * Work.Spaces.pz (Work.Spaces.DzIter 2 g) z θ
          - z * Work.Spaces.pz (Work.Spaces.DzIter 1 g) z θ
    ring
  rw [hdec, hrhs]

/-! ### `Q` commutes with `D_θ` -/

/-- On the open quadrant, `D_z` and `D_θ` commute (pointwise Clairaut; `C²` suffices). -/
theorem Q0_Dz_Dth_comm (hg : SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth g)))
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz g))) Q0 := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := mem_Q0.mp hp
  exact Work.Spaces.Dz_Dth_comm (contDiffAt_two_of_mem hg h1 ⟨h2, h3⟩)

/-- On the open quadrant, `D_z²` commutes with `D_θ`: `D_z²(D_θ g) = D_θ(D_z² g)`. -/
theorem Q0_DzIter2_Dth_comm (hg : SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter 2 (Work.Spaces.Dth g)))
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter 2 g))) Q0 := by
  have h1 : Set.EqOn
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.Dth g))))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.Dz g)))) Q0 :=
    Q0_Dz_congr (Q0_Dz_Dth_comm hg)
  have h2 : Set.EqOn
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.Dz g))))
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.Dz g)))) Q0 :=
    Q0_Dz_Dth_comm hg.Dz
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h1.trans h2

/-- On the open quadrant, `Q = z²∂_z²` commutes with `D_θ = sin(2θ)∂_θ`. -/
theorem Qop_Dth_eq (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Qop (Work.Spaces.Dth g) z θ = Work.Spaces.Dth (Qop g) z θ := by
  have hmem : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hEqOn : Set.EqOn (Function.uncurry (Qop g))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter 2 g z θ
        - Work.Spaces.DzIter 1 g z θ)) Q0 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_Q0.mp hp
    exact Qop_eq_Dz2_sub_Dz hg h1 ⟨h2, h3⟩
  have hpthcongr : Work.Spaces.pth (Qop g) z θ
      = Work.Spaces.pth (fun z θ => Work.Spaces.DzIter 2 g z θ
          - Work.Spaces.DzIter 1 g z θ) z θ :=
    Work.Spaces.pth_congr_of_isOpen isOpen_Q0 hEqOn hmem
  have hsub : Work.Spaces.pth (fun z θ => Work.Spaces.DzIter 2 g z θ
        - Work.Spaces.DzIter 1 g z θ) z θ
      = Work.Spaces.pth (Work.Spaces.DzIter 2 g) z θ
        - Work.Spaces.pth (Work.Spaces.DzIter 1 g) z θ :=
    Q0_pth_sub (differentiableAt_slice_θ_of (hg.DzIter 2) hz hθ)
      (differentiableAt_slice_θ_of (hg.DzIter 1) hz hθ)
  have e1 : Work.Spaces.DzIter 2 (Work.Spaces.Dth g) z θ
      = Work.Spaces.Dth (Work.Spaces.DzIter 2 g) z θ :=
    Q0_DzIter2_Dth_comm hg hmem
  have e2 : Work.Spaces.DzIter 1 (Work.Spaces.Dth g) z θ
      = Work.Spaces.Dth (Work.Spaces.DzIter 1 g) z θ :=
    Q0_Dz_Dth_comm hg hmem
  have hdec : Qop (Work.Spaces.Dth g) z θ
      = Work.Spaces.Dth (Work.Spaces.DzIter 2 g) z θ
        - Work.Spaces.Dth (Work.Spaces.DzIter 1 g) z θ := by
    rw [Qop_eq_Dz2_sub_Dz (hg.Dth) hz hθ, e1, e2]
  have hrhs : Work.Spaces.Dth (Qop g) z θ
      = Work.Spaces.Dth (Work.Spaces.DzIter 2 g) z θ
        - Work.Spaces.Dth (Work.Spaces.DzIter 1 g) z θ := by
    show Real.sin (2 * θ) * Work.Spaces.pth (Qop g) z θ
        = Work.Spaces.Dth (Work.Spaces.DzIter 2 g) z θ
          - Work.Spaces.Dth (Work.Spaces.DzIter 1 g) z θ
    rw [hpthcongr, hsub]
    show Real.sin (2 * θ) * (Work.Spaces.pth (Work.Spaces.DzIter 2 g) z θ
          - Work.Spaces.pth (Work.Spaces.DzIter 1 g) z θ)
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 2 g) z θ
          - Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 1 g) z θ
    ring
  rw [hdec, hrhs]

/-! ### The iterated versions -/

/-- On the open quadrant, `Q = z²∂_z²` commutes with every iterate of `D_z`. -/
theorem Qop_DzIter_eq (hg : SmoothOpen g) (m : ℕ) :
    Set.EqOn (Function.uncurry (Qop (Work.Spaces.DzIter m g)))
      (Function.uncurry (Work.Spaces.DzIter m (Qop g))) Q0 := by
  induction m with
  | zero => intro p hp; rfl
  | succ m ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ1, hθ2⟩ := mem_Q0.mp hp
      have h1 : Qop (Work.Spaces.DzIter (m + 1) g) z θ
          = Work.Spaces.Dz (Qop (Work.Spaces.DzIter m g)) z θ :=
        Qop_Dz_eq (hg.DzIter m) hz ⟨hθ1, hθ2⟩
      have h2 : Work.Spaces.Dz (Qop (Work.Spaces.DzIter m g)) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter m (Qop g)) z θ :=
        Q0_Dz_congr (A := Qop (Work.Spaces.DzIter m g))
          (B := Work.Spaces.DzIter m (Qop g)) ih hp
      show Qop (Work.Spaces.DzIter (m + 1) g) z θ
          = Work.Spaces.DzIter (m + 1) (Qop g) z θ
      rw [h1, h2]
      simp only [Work.Spaces.DzIter_succ]

/-- On the open quadrant, `Q = z²∂_z²` commutes with every iterate of `D_θ`. -/
theorem Qop_DthIter_eq (hg : SmoothOpen g) (i : ℕ) :
    Set.EqOn (Function.uncurry (Qop (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Qop g))) Q0 := by
  induction i with
  | zero => intro p hp; rfl
  | succ i ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ1, hθ2⟩ := mem_Q0.mp hp
      have h1 : Qop (Work.Spaces.DthIter (i + 1) g) z θ
          = Work.Spaces.Dth (Qop (Work.Spaces.DthIter i g)) z θ :=
        Qop_Dth_eq (hg.DthIter i) hz ⟨hθ1, hθ2⟩
      have h2 : Work.Spaces.Dth (Qop (Work.Spaces.DthIter i g)) z θ
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Qop g)) z θ := by
        have hstep := Work.Spaces.pth_congr_of_isOpen
          (f := Qop (Work.Spaces.DthIter i g))
          (f' := Work.Spaces.DthIter i (Qop g)) isOpen_Q0 ih hp
        show Real.sin (2 * θ) * Work.Spaces.pth (Qop (Work.Spaces.DthIter i g)) z θ
            = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter i (Qop g)) z θ
        rw [hstep]
      show Qop (Work.Spaces.DthIter (i + 1) g) z θ
          = Work.Spaces.DthIter (i + 1) (Qop g) z θ
      rw [h1, h2]
      simp only [Work.Spaces.DthIter_succ]

/-- **`z² ∂_z²` commutes with the iterated operators `D_z^m D_θ^i` on the open quadrant.**

For `f` smooth on the open quadrant `Q0 = (0,∞) × (0,π/2)` and all `m, i : ℕ`, the operator
`Q = z²∂_z²` (i.e. `fun z θ => z² · pzIter 2 f z θ`) commutes with `D_z^m D_θ^i`:

`z² ∂_z² (D_z^m D_θ^i f) = D_z^m D_θ^i (z² ∂_z² f)`  on `Q0`.

Route.  As operators, `z²∂_z² = D_z² - D_z = D_z(D_z - 1)`, hence `z²∂_z²` is a polynomial in
`D_z` and commutes with `D_z^m`; it also commutes with `D_θ^i`, because
`D_z (D_θ^i g) = D_θ^i (D_z g)` on the open quadrant (`Work.Spaces.DzDthIterCommOn` applied with
`V` the open quadrant), so that
`z²∂_z²(D_θ^i g) = D_z²(D_θ^i g) - D_z(D_θ^i g) = D_θ^i(D_z²g) - D_θ^i(D_zg) = D_θ^i(z²∂_z²g)`.
The pointwise identity `z²∂_z²(D_z g) = D_z(z²∂_z² g)` (the one-variable statement
`z²(zh')'' = z(z²h'')'`, i.e. `z²(z h')'' - z(z²h'')' = 0`, provable by differentiating
products: both sides equal `z³h''' + 2z²h''`) gives the induction on `m`.  Nothing here needs any
integrability hypothesis. -/
theorem ZsqPz2Comm (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) (m i : ℕ) :
    Set.EqOn (Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z θ))
      (Function.uncurry (Work.Spaces.mixed m i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h1 := Qop_DzIter_eq (hf.DthIter i) m
  have h2 := Qop_DthIter_eq hf i
  have h3 := Q0_DzIter_congr h2 m
  exact h1.trans h3

end Work.FTS.EllipticEst.DzAmgm
