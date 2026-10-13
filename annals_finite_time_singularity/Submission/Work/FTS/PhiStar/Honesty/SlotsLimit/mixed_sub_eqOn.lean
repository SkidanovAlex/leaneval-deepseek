/-
# `FTS/PhiStar/Honesty/SlotsLimit/mixed_sub_eqOn` — linearity of `D_z^j D_θ^i` on the open
quadrant

The limit passage of `Work.FTS.PhiStar.Honesty.hkMem_slots_of_approx` has to move between the
slot *of the difference* `Ψ_n - Φ` and the *difference of the slots* of `Ψ_n` and `Φ`.  On the
open quadrant `Q0 = (0,∞) × (0,π/2)` the operators are honest differential operators and the
smoothness hypothesis `SmoothOpen` supplies the differentiability of every slice needed, so the
identity is formal linearity of `deriv` on each slice.

What is proved here (`sorry`-free):

* `Dz_sub_point` / `Dth_sub_point`: pointwise on `Q0`,
  `D_z (A-B) = D_z A - D_z B`, `D_θ (A-B) = D_θ A - D_θ B` for `SmoothOpen A`, `SmoothOpen B`
  (using `deriv_sub` and `SmoothOpen.hasDerivAt_slice` resp. the differentiability of the
  `θ`-slice from `SmoothOpen.curry_θ`);
* `Dz_congr_Q0` / `Dth_congr_Q0` and their iterates `DzIter_congr_Q0` / `DthIter_congr_Q0`:
  only the values on the open quadrant matter — the `z`- (resp. `θ`-) derivative at an interior
  point is a germ limit, and a neighbourhood of that point inside `Q0` is again contained in
  `Q0` (`Filter.EventuallyEq.deriv_eq`).  No smoothness is needed for these;
* the iterated linearity `DzIter_sub_eqOn`, `DthIter_sub_eqOn` and the mixed
  `mixed_sub_eqOn_of_smoothOpen`, assembled from the two ingredients above.

The requested theorem `mixed_sub_eqOn` is the `(A,B) = (f,g)` instance.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## Pointwise linearity of `D_z` and `D_θ` on the open quadrant -/

/-- **`D_z` commutes with subtraction on `Q0`.**  The only content is `deriv_sub` on the
`z`-slice, whose differentiability is `SmoothOpen.hasDerivAt_slice`. -/
lemma Dz_sub_point {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dz (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.Dz A z θ - Work.Spaces.Dz B z θ := by
  have hda := hA.hasDerivAt_slice hθ hz
  have hdb := hB.hasDerivAt_slice hθ hz
  have hfun : (fun z' : ℝ => A z' θ - B z' θ)
      = (fun z' : ℝ => A z' θ) - (fun z' => B z' θ) := rfl
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hfun, deriv_sub hda.differentiableAt hdb.differentiableAt]
  ring

/-- **`D_θ` commutes with subtraction on `Q0`.**  Here the differentiability of the two
`θ`-slices comes from `SmoothOpen.curry_θ` (a `C^∞` function has differentiable slices). -/
lemma Dth_sub_point {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.Dth A z θ - Work.Spaces.Dth B z θ := by
  have hdA : DifferentiableAt ℝ (fun θ' : ℝ => A z θ') θ :=
    ((hA.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hdB : DifferentiableAt ℝ (fun θ' : ℝ => B z θ') θ :=
    ((hB.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hfun : (fun θ' : ℝ => A z θ' - B z θ')
      = (fun θ' : ℝ => A z θ') - (fun θ' => B z θ') := rfl
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hfun, deriv_sub hdA hdB]
  ring

/-! ## Congruence on `Q0`: only the values inside the open quadrant matter -/

/-- **`D_z` is local on `Q0`.**  If `A` and `B` agree on the open quadrant then so do `D_z A`
and `D_z B`: at an interior point the `z`-derivative is a germ limit, and a neighbourhood of
the point inside `Q0` is again contained in `Q0`. -/
lemma Dz_congr_Q0 {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz A))
      (Function.uncurry (Work.Spaces.Dz B)) Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ :=
    Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  have hev : (fun z' : ℝ => A z' p.2) =ᶠ[𝓝 p.1] (fun z' : ℝ => B z' p.2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ0, hθ1⟩)
  simp only [Function.uncurry, Work.Spaces.Dz, Work.Spaces.pz]
  rw [Filter.EventuallyEq.deriv_eq hev]

/-- **`D_θ` is local on `Q0`.** -/
lemma Dth_congr_Q0 {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth A))
      (Function.uncurry (Work.Spaces.Dth B)) Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ :=
    Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  have hev : (fun θ' : ℝ => A p.1 θ') =ᶠ[𝓝 p.2] (fun θ' : ℝ => B p.1 θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show p.2 ∈ Set.Ioo 0 (π / 2) from ⟨hθ0, hθ1⟩)] with θ' hθ'
    exact h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩)
  simp only [Function.uncurry, Work.Spaces.Dth, Work.Spaces.pth]
  rw [Filter.EventuallyEq.deriv_eq hev]

/-- **The iterates `D_z^n` are local on `Q0`.** -/
lemma DzIter_congr_Q0 {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) (n : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter n A))
      (Function.uncurry (Work.Spaces.DzIter n B)) Q0 := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa only [Work.Spaces.DzIter_succ] using Dz_congr_Q0 ih

/-- **The iterates `D_θ^n` are local on `Q0`.** -/
lemma DthIter_congr_Q0 {A B : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry A) (Function.uncurry B) Q0) (n : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter n A))
      (Function.uncurry (Work.Spaces.DthIter n B)) Q0 := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa only [Work.Spaces.DthIter_succ] using Dth_congr_Q0 ih

/-! ## The `EqOn`-form of the pointwise identities -/

/-- `D_z (A - B) = D_z A - D_z B` on the open quadrant. -/
lemma Dz_sub_eqOn {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (fun z θ => A z θ - B z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.Dz A z θ - Work.Spaces.Dz B z θ)) Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ :=
    Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  exact Dz_sub_point hA hB hz ⟨hθ0, hθ1⟩

/-- `D_θ (A - B) = D_θ A - D_θ B` on the open quadrant. -/
lemma Dth_sub_eqOn {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (fun z θ => A z θ - B z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.Dth A z θ - Work.Spaces.Dth B z θ)) Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ :=
    Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  exact Dth_sub_point hA hB hz ⟨hθ0, hθ1⟩

/-- **`D_z^n` commutes with subtraction on `Q0`.**  Induction on `n`, using that a `D_z`-iterate
of a `SmoothOpen` function is again `SmoothOpen` (so `Dz_sub_point` applies) together with the
localisation `Dz_congr_Q0`, which transfers the induction hypothesis into the argument of `D_z`. -/
lemma DzIter_sub_eqOn {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B)
    (n : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter n (fun z θ => A z θ - B z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter n A z θ
        - Work.Spaces.DzIter n B z θ)) Q0 := by
  induction n with
  | zero => intro p hp; rfl
  | succ n ih =>
    have hcongr := Dz_congr_Q0 ih
    have hsub := Dz_sub_eqOn (hA.DzIter n) (hB.DzIter n)
    intro p hp
    calc Function.uncurry (Work.Spaces.DzIter (n + 1) (fun z θ => A z θ - B z θ)) p
        = Function.uncurry (Work.Spaces.Dz
            (Work.Spaces.DzIter n (fun z θ => A z θ - B z θ))) p := rfl
      _ = Function.uncurry (Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter n A z θ
              - Work.Spaces.DzIter n B z θ)) p := hcongr hp
      _ = Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.DzIter n A) z θ
              - Work.Spaces.Dz (Work.Spaces.DzIter n B) z θ) p := hsub hp
      _ = Function.uncurry (fun z θ => Work.Spaces.DzIter (n + 1) A z θ
              - Work.Spaces.DzIter (n + 1) B z θ) p := rfl

/-- **`D_θ^n` commutes with subtraction on `Q0`.** -/
lemma DthIter_sub_eqOn {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B)
    (n : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter n (fun z θ => A z θ - B z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DthIter n A z θ
        - Work.Spaces.DthIter n B z θ)) Q0 := by
  induction n with
  | zero => intro p hp; rfl
  | succ n ih =>
    have hcongr := Dth_congr_Q0 ih
    have hsub := Dth_sub_eqOn (hA.DthIter n) (hB.DthIter n)
    intro p hp
    calc Function.uncurry (Work.Spaces.DthIter (n + 1) (fun z θ => A z θ - B z θ)) p
        = Function.uncurry (Work.Spaces.Dth
            (Work.Spaces.DthIter n (fun z θ => A z θ - B z θ))) p := rfl
      _ = Function.uncurry (Work.Spaces.Dth (fun z θ => Work.Spaces.DthIter n A z θ
              - Work.Spaces.DthIter n B z θ)) p := hcongr hp
      _ = Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.DthIter n A) z θ
              - Work.Spaces.Dth (Work.Spaces.DthIter n B) z θ) p := hsub hp
      _ = Function.uncurry (fun z θ => Work.Spaces.DthIter (n + 1) A z θ
              - Work.Spaces.DthIter (n + 1) B z θ) p := rfl

/-! ## The mixed operator -/

/-- **`mixed j i = D_z^j D_θ^i` commutes with subtraction on `Q0`** (general `SmoothOpen` data;
the requested theorem is the instance `A = f`, `B = g`). -/
lemma mixed_sub_eqOn_of_smoothOpen {A B : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hB : Work.FTS.EllipticEst.SmoothOpen B)
    (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i (fun z θ => A z θ - B z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.mixed j i A z θ
        - Work.Spaces.mixed j i B z θ)) Q0 := by
  have h2 := DzIter_congr_Q0 (DthIter_sub_eqOn hA hB i) j
  have h3 := DzIter_sub_eqOn (hA.DthIter i) (hB.DthIter i) j
  intro p hp
  calc Function.uncurry (Work.Spaces.mixed j i (fun z θ => A z θ - B z θ)) p
      = Function.uncurry (Work.Spaces.DzIter j
          (Work.Spaces.DthIter i (fun z θ => A z θ - B z θ))) p := rfl
    _ = Function.uncurry (Work.Spaces.DzIter j (fun z θ => Work.Spaces.DthIter i A z θ
            - Work.Spaces.DthIter i B z θ)) p := h2 hp
    _ = Function.uncurry (fun z θ => Work.Spaces.DzIter j (Work.Spaces.DthIter i A) z θ
            - Work.Spaces.DzIter j (Work.Spaces.DthIter i B) z θ) p := h3 hp
    _ = Function.uncurry (fun z θ => Work.Spaces.mixed j i A z θ
            - Work.Spaces.mixed j i B z θ) p := rfl

/-- **The mixed operators are linear on the open quadrant.**  For `f`, `g` smooth on `Q0` and all
`j`, `i`, the operator `mixed j i = D_z^j D_θ^i` commutes with subtraction on `Q0`.  This is the
pointwise identity needed to move between the slot *of the difference* and the *difference of the
slots* (both occur in the limit passage). -/
theorem mixed_sub_eqOn {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i (fun z θ => f z θ - g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.mixed j i f z θ
        - Work.Spaces.mixed j i g z θ))
      Work.FTS.EllipticEst.Q0 :=
  mixed_sub_eqOn_of_smoothOpen hf hg j i

end Work.FTS.PhiStar.Honesty.SlotsLimit
