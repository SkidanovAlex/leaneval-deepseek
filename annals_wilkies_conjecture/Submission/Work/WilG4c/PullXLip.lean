import Mathlib
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4b.xDeriv_eq
import Submission.Work.WilG4c.Pullback
import Submission.Work.WilG4c.contDiffAt_famFunHat_xPt

/-!
  WilG4c / PullXLip — the `x`-Lipschitz bound for an affine `x`-pullback.

  Let `f : (Fin p → ℝ) → (Fin (n+1) → ℝ) → ℝ` be a family member and `γ : ℝ → (Fin n → ℝ)`
  a curve in the cube which is, for each `x` in the interval, a point at which the
  `x`-derivative is within a factor `2` of the (fibre) maximum.  The chain rule along
  `s ↦ (x, γ(x))` gives

      ∂₀ f (x, γ x) = d/ds [f (cons s (γ s))] (x) - ∑_j ∂_j f (x, γ x) · γ_j'(x),

  so that, using `‖∂_j f‖ ≤ 1` (`hyb`), `|d/ds [f (cons s (γ s))]| β ≤ 1` (`hcb`) and
  `|γ_j'| β ≤ 1` (`hγb`),

      |∂₀ f (x, γ x)| · β ≤ 1 + n,

  whence `|∂₀ f (x, y)| · β ≤ 2 (n+1)` for every `y` in the cube.

  The auxiliary `σ`-shift `z ↦ Fin.append l z` is used to move between the
  `famFunHat`-point of `ℝ^{p + (n+1)}` and the family member in the parameter `l`; its
  derivative is the continuous linear map `v ↦ Fin.append 0 v`.
-/

noncomputable section

open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ## 1. The `σ`-shift `z ↦ Fin.append 0 z` as a continuous linear map -/

/-- `v ↦ Fin.append 0 v` (parameter coordinates set to `0`), as a linear map. -/
def pullX_appendLm (p n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin (p + n) → ℝ) where
  toFun v := Fin.append (0 : Fin p → ℝ) v
  map_add' v w := by
    funext i
    induction i using Fin.addCases with
    | left a => simp [Fin.append_left]
    | right b => simp [Fin.append_right]
  map_smul' c v := by
    funext i
    induction i using Fin.addCases with
    | left a => simp [Fin.append_left]
    | right b => simp [Fin.append_right]

/-- `v ↦ Fin.append 0 v` as a continuous linear map. -/
def pullX_appendCLM (p n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (p + n) → ℝ) :=
  (pullX_appendLm p n).toContinuousLinearMap

@[simp] theorem pullX_appendCLM_apply (p n : ℕ) (v : Fin n → ℝ) :
    pullX_appendCLM p n v = Fin.append (0 : Fin p → ℝ) v := rfl

/-- The affine map `z ↦ Fin.append l z` is the constant `Fin.append l 0` plus the linear
map `Fin.append 0`. -/
theorem pullX_fin_append_const_add (p n : ℕ) (l : Fin p → ℝ) (v : Fin n → ℝ) :
    Fin.append l v = Fin.append l 0 + pullX_appendCLM p n v := by
  funext i
  induction i using Fin.addCases with
  | left a => simp [Fin.append_left, pullX_appendCLM_apply, Pi.add_apply]
  | right b => simp [Fin.append_right, pullX_appendCLM_apply, Pi.add_apply]

/-- The map `z ↦ Fin.append l z` is differentiable with derivative `Fin.append 0`. -/
theorem pullX_hasFDerivAt_finAppend (p n : ℕ) (l : Fin p → ℝ) (z : Fin n → ℝ) :
    HasFDerivAt (fun z : Fin n → ℝ => Fin.append l z) (pullX_appendCLM p n) z := by
  have hfun : (fun z : Fin n → ℝ => Fin.append l z)
      = fun z => Fin.append l (0 : Fin n → ℝ) + pullX_appendCLM p n z := by
    funext z; exact pullX_fin_append_const_add p n l z
  rw [hfun]
  exact (pullX_appendCLM p n).hasFDerivAt.const_add (Fin.append l 0)

/-- The `σ`-shift sends the standard basis vector at `k` to the standard basis vector at
the corresponding coordinate of `Fin (p + n)`. -/
theorem pullX_fin_append_zero_single (p n : ℕ) (k : Fin n) :
    Fin.append (0 : Fin p → ℝ) (Pi.single k 1) = Pi.single (Fin.natAdd p k) 1 := by
  funext i
  induction i using Fin.addCases with
  | left a =>
    rw [Fin.append_left]
    have hne : Fin.castAdd n a ≠ Fin.natAdd p k := by
      intro h
      have h1 : (Fin.castAdd n a).val = (Fin.natAdd p k).val := by rw [h]
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
      omega
    rw [Pi.single_eq_of_ne hne]; rfl
  | right b =>
    rw [Fin.append_right]
    by_cases h : b = k
    · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]
    · have hne : Fin.natAdd p b ≠ Fin.natAdd p k := fun hh => h ((Fin.natAdd_inj p).mp hh)
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne h]

/-! ## 2. Transferring Fréchet derivatives across the `σ`-shift -/

/-- The Fréchet derivative of the family member in the parameter `l` at `z` is the Fréchet
derivative of `famFunHat F` at `Fin.append l z`, evaluated on the `σ`-shift of the
direction. -/
theorem pullX_fderiv_famFunHat_xPt {p n : ℕ}
    (F : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (hd : DifferentiableAt ℝ (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y))
    (v : Fin (n + 1) → ℝ) :
    fderiv ℝ (F l) (Fin.cons x y) v
      = fderiv ℝ (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y) (Fin.append 0 v) := by
  have hd' : DifferentiableAt ℝ (Work.WilkG4c.famFunHat F) (Fin.append l (Fin.cons x y)) := hd
  have hcomp := HasFDerivAt.comp (x := Fin.cons x y)
    (f := fun z : Fin (n + 1) → ℝ => Fin.append l z)
    (hd'.hasFDerivAt) (pullX_hasFDerivAt_finAppend p (n + 1) l (Fin.cons x y))
  have hfun : (Work.WilkG4c.famFunHat F) ∘ (fun z : Fin (n + 1) → ℝ => Fin.append l z)
      = F l := by
    funext z
    simp [Function.comp, Work.WilkG4c.famFunHat, Fin.append_left, Fin.append_right]
  rw [hfun] at hcomp
  have hkey := hcomp.fderiv
  rw [hkey, ContinuousLinearMap.comp_apply, pullX_appendCLM_apply]
  rfl

/-- The `x`-derivative of a family member is the Fréchet derivative of the member in the
parameter `l`, evaluated on the `x`-basis vector. -/
theorem pullX_xDeriv_eq_fderiv {p n : ℕ}
    (F : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (hd : DifferentiableAt ℝ (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y)) :
    Work.WilkG4c.xDeriv F l x y
      = fderiv ℝ (F l) (Fin.cons x y) (Pi.single (0 : Fin (n + 1)) 1) := by
  rw [Work.WilkG4c.xDeriv]
  rw [show Work.WilkG4c.xDirHat p n = Fin.natAdd p 0 from rfl]
  rw [pullX_fderiv_famFunHat_xPt F l x y hd (Pi.single (0 : Fin (n + 1)) 1)]
  rw [pullX_fin_append_zero_single p (n + 1) 0]

/-- The `y`-derivative of a family member, transferred the other way: the `famFunHat`
`y`-basis derivative is the `y`-basis derivative of the member in the parameter `l`. -/
theorem pullX_fderiv_yDir_eq {p n : ℕ}
    (F : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (j : Fin n)
    (hd : DifferentiableAt ℝ (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y)) :
    fderiv ℝ (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y)
        (Pi.single (Fin.natAdd p j.succ) 1)
      = fderiv ℝ (F l) (Fin.cons x y) (Pi.single j.succ 1) := by
  rw [pullX_fderiv_famFunHat_xPt F l x y hd (Pi.single j.succ 1)]
  rw [pullX_fin_append_zero_single p (n + 1) j.succ]

/-! ## 3. The main bound -/

theorem PullXLip {p n : ℕ} (F : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (α β : (Fin p → ℝ) → ℝ) (l : Fin p → ℝ)
    (hβ : 0 < β l) (hα : 0 ≤ α l) (hαβ : α l + β l ≤ 1)
    (hγc : ∀ x ∈ Set.Ioo (α l) (α l + β l), γ l x ∈ WilkiesDesign.openCube n)
    (hC1 : ∀ x ∈ Set.Ioo (α l) (α l + β l), ∀ y ∈ WilkiesDesign.openCube n,
      ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y))
    (hyb : ∀ x ∈ Set.Ioo (α l) (α l + β l), ∀ y ∈ WilkiesDesign.openCube n, ∀ j : Fin n,
      |fderiv ℝ (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y)
        (Pi.single (Fin.natAdd p j.succ) 1)| ≤ 1)
    (hmax : ∀ x ∈ Set.Ioo (α l) (α l + β l), ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv F l x y| ≤ 2 * |Work.WilkG4c.xDeriv F l x (γ l x)|)
    (hγC1 : ∀ j : Fin n, ContDiffOn ℝ 1 (fun s : ℝ => γ l s j) (Set.Ioo (α l) (α l + β l)))
    (hγb : ∀ x ∈ Set.Ioo (α l) (α l + β l), ∀ j : Fin n,
      |deriv (fun s : ℝ => γ l s j) x| * β l ≤ 1)
    (hcb : ∀ x ∈ Set.Ioo (α l) (α l + β l),
      |deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x| * β l ≤ 1)
    (hcC1 : ContDiffOn ℝ 1 (fun s : ℝ => F l (Fin.cons s (γ l s))) (Set.Ioo (α l) (α l + β l))) :
    ∀ x ∈ Set.Ioo (α l) (α l + β l), ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv F l x y| * β l ≤ 2 * ((n : ℝ) + 1) := by
  intro x hx y hy
  have hβnn : 0 ≤ β l := le_of_lt hβ
  have hγcx : γ l x ∈ WilkiesDesign.openCube n := hγc x hx
  have hd : DifferentiableAt ℝ (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x (γ l x)) :=
    (hC1 x hx (γ l x) hγcx).differentiableAt_one
  -- The key bound: at the near-maximiser `γ l x` the scaled `x`-derivative is `≤ n + 1`.
  have hmain : |Work.WilkG4c.xDeriv F l x (γ l x)| * β l ≤ (n : ℝ) + 1 := by
    have hxC1 : ContDiffAt ℝ 1 (F l) (Fin.cons x (γ l x)) :=
      Work.WilkG4c.contDiffAt_famFunHat_xPt F l x (γ l x) (hC1 x hx (γ l x) hγcx)
    have hγi : ∀ i : Fin n, HasDerivAt (fun s : ℝ => γ l s i)
        (deriv (fun s : ℝ => γ l s i) x) x := by
      intro i
      exact ((hγC1 i).contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt_one.hasDerivAt
    have hφ : HasDerivAt (fun s : ℝ => F l (Fin.cons s (γ l s)))
        (deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x) x :=
      (hcC1.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt_one.hasDerivAt
    -- The chain rule identity of `Work.WilG4b.xDeriv_eq`.
    have hkey := Work.WilG4b.xDeriv_eq (F l) (γ l) x
        (deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x)
        (fun i : Fin n => deriv (fun s : ℝ => γ l s i) x) hxC1 hγi hφ
    have hx0 := pullX_xDeriv_eq_fderiv F l x (γ l x) hd
    rw [hx0, hkey]
    set φ' : ℝ := deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x with hφ'def
    set S : ℝ := ∑ i : Fin n, fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)
        * deriv (fun s : ℝ => γ l s i) x with hSdef
    have hphi_b : |φ'| * β l ≤ 1 := by rw [hφ'def]; exact hcb x hx
    have hB : ∀ i : Fin n,
        |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)| ≤ 1 := by
      intro i
      rw [← pullX_fderiv_yDir_eq F l x (γ l x) i hd]
      exact hyb x hx (γ l x) hγcx i
    have hSbound : |S| * β l ≤ (n : ℝ) := by
      have htri : |S| ≤ ∑ i : Fin n,
          |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
            * |deriv (fun s : ℝ => γ l s i) x| := by
        rw [hSdef]
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul]
      calc |S| * β l
          ≤ (∑ i : Fin n, |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
              * |deriv (fun s : ℝ => γ l s i) x|) * β l :=
            mul_le_mul_of_nonneg_right htri hβnn
        _ = ∑ i : Fin n, (|fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
              * |deriv (fun s : ℝ => γ l s i) x|) * β l := by rw [Finset.sum_mul]
        _ = ∑ i : Fin n, |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
              * (|deriv (fun s : ℝ => γ l s i) x| * β l) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ ≤ ∑ _i : Fin n, (1 : ℝ) * 1 := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul (hB i) (hγb x hx i) (mul_nonneg (abs_nonneg _) hβnn) zero_le_one
        _ = (n : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have htri2 : |φ' - S| ≤ |φ'| + |S| := by
      have := abs_add_le φ' (-S)
      simpa [sub_eq_add_neg] using this
    calc |φ' - S| * β l ≤ (|φ'| + |S|) * β l := mul_le_mul_of_nonneg_right htri2 hβnn
      _ = |φ'| * β l + |S| * β l := by ring
      _ ≤ 1 + n := add_le_add hphi_b hSbound
      _ = (n : ℝ) + 1 := by ring
  -- Finally use the near-maximality of `γ l x` on the fibre.
  have h2 : |Work.WilkG4c.xDeriv F l x y| ≤ 2 * |Work.WilkG4c.xDeriv F l x (γ l x)| :=
    hmax x hx y hy
  calc |Work.WilkG4c.xDeriv F l x y| * β l
      ≤ (2 * |Work.WilkG4c.xDeriv F l x (γ l x)|) * β l :=
        mul_le_mul_of_nonneg_right h2 hβnn
    _ = 2 * (|Work.WilkG4c.xDeriv F l x (γ l x)| * β l) := by ring
    _ ≤ 2 * ((n : ℝ) + 1) := by linarith [hmain]

end Work.WilG4c
