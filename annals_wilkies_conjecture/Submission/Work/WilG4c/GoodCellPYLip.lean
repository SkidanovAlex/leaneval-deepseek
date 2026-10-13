import Mathlib
import Submission.Work.WilG4c.PullXLip
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.StepLipAux
import Submission.Work.WilG4b.xDeriv_eq
import Submission.Work.WilG4c.PullXLipOn
import Submission.Work.WilG4c.SliceLipInY
import Submission.Work.WilG4c.SliceLipInX
import Submission.Work.WilG4c.PsiLipOnI

/-!
  WilG4c / GoodCellPYLip — the per-cell "good cell" engine of BNZ §5.3.

  Let `F : ℝ^p → ℝ^{n+1} → ℝ` be a `k`-tuple of family members on the cell whose `x`-range is
  parametrised by `ψ l : I → (u,v)`, and let `γ`, `β` be the near-maximising curves and the
  chart radii of `Work.WilkG4c.PullXLip`, all of whose conditions hold on the interval `(u,v)`
  (the *cell* interval, not `I`).  Then the pulled-back family

      `G i l z = F i l (Fin.cons (ψ l (z 0)) (Fin.tail z))`

  again satisfies BNZ's `PY` bounds (`‖D^m_y G‖ ≤ 1` for `m ≤ r`, at `x ∈ I`) and is Lipschitz
  on the cube with the constant `max (2(n+1)) 1 * (n+1)`.

  The `PY` part needs no chain rule at all: the `y`-coordinates are left untouched, so

      `slice (G i l) x = slice (F i l) (ψ l x)`   (`x ∈ I`),

  and `ψ l` maps `I` into `(u,v)` (`hψI`), where the `PY` bounds of the cell are stated.

  The Lipschitz part is the two-step mean value inequality of BNZ §5.3:

  * **`y`-directions** (`Work.WilG4c.SliceLipInY`): the `PY`-bounds `hyb` make the covector
    `D_y (F i l)` have `ℓ¹`-norm `≤ n`, whence `n`-Lipschitz in `y` on the cube;
  * **`x`-direction** (`Work.WilG4c.SliceLipInX`): `PullXLipOn` gives
    `|∂ₓ F| · β l ≤ 2(n+1)`, so the slices are `2(n+1)/β l`-Lipschitz in `x`;
  * **the parametrisation** (`Work.WilG4c.PsiLipOnI`): `|ψ l a - ψ l b| ≤ β l |a - b|`, and the
    `β l` cancels against the `1/β l` of the `x`-step, leaving `2(n+1) |z 0 - z' 0|`.

  Adding the two contributions gives `(3n+2) · dist ≤ max (2(n+1)) 1 * (n+1) · dist`; the
  coordinatewise (sup-metric) estimate `‖v‖₁ ≤ (n+1)‖v‖∞` is what produces the `(n+1)` factor.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

theorem GoodCellPYLip {p n k r : ℕ} (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1))
    (γ : Fin k → (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (β : (Fin p → ℝ) → ℝ)
    (ψ : (Fin p → ℝ) → ℝ → ℝ) (u v : ℝ)
    (hβ : ∀ l ∈ Λ, 0 < β l)
    (hψI : ∀ l ∈ Λ, ∀ s ∈ Work.WilkG4c.I, u < ψ l s ∧ ψ l s < v)
    (hψb : ∀ l ∈ Λ, ∀ s ∈ Work.WilkG4c.I, |deriv (ψ l) s| ≤ β l)
    (hψC1 : ∀ l ∈ Λ, ContDiffOn ℝ 1 (ψ l) Work.WilkG4c.I)
    (hγc : ∀ i, ∀ l ∈ Λ, ∀ x ∈ Set.Ioo u v, γ i l x ∈ WilkiesDesign.openCube n)
    (hC1 : ∀ i, ∀ l ∈ Λ, ∀ x ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n,
      ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (F i)) (Work.WilkG4c.xPt l x y))
    (hyb : ∀ i, ∀ l ∈ Λ, ∀ x ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n, ∀ j : Fin n,
      |fderiv ℝ (Work.WilkG4c.famFunHat (F i)) (Work.WilkG4c.xPt l x y)
        (Pi.single (Fin.natAdd p j.succ) 1)| ≤ 1)
    (hmax : ∀ i, ∀ l ∈ Λ, ∀ x ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv (F i) l x y| ≤ 2 * |Work.WilkG4c.xDeriv (F i) l x (γ i l x)|)
    (hγC1 : ∀ i, ∀ l ∈ Λ, ∀ j : Fin n, ContDiffOn ℝ 1 (fun s : ℝ => γ i l s j) (Set.Ioo u v))
    (hγb : ∀ i, ∀ l ∈ Λ, ∀ x ∈ Set.Ioo u v, ∀ j : Fin n,
      |deriv (fun s : ℝ => γ i l s j) x| * β l ≤ 1)
    (hcb : ∀ i, ∀ l ∈ Λ, ∀ x ∈ Set.Ioo u v,
      |deriv (fun s : ℝ => F i l (Fin.cons s (γ i l s))) x| * β l ≤ 1)
    (hcC1 : ∀ i, ∀ l ∈ Λ, ContDiffOn ℝ 1 (fun s : ℝ => F i l (Fin.cons s (γ i l s)))
      (Set.Ioo u v))
    (hY : ∀ i, ∀ l ∈ Λ, ∀ x ∈ Set.Ioo u v, ∀ m, m ≤ r → ∀ y ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (F i l) x) y‖ ≤ 1) :
    (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ y ∈ WilkiesDesign.openCube n,
        ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (fun z : Fin (n + 1) → ℝ => F i l
          (Fin.cons (ψ l (z 0)) (Fin.tail z))) x) y‖ ≤ 1) ∧
      (∀ i, ∀ l ∈ Λ, ∀ z z' : Fin (n + 1) → ℝ,
        z ∈ WilkiesDesign.openCube (n + 1) → z' ∈ WilkiesDesign.openCube (n + 1) →
        |F i l (Fin.cons (ψ l (z 0)) (Fin.tail z)) - F i l (Fin.cons (ψ l (z' 0)) (Fin.tail z'))| ≤
          (max (2 * ((n : ℝ) + 1)) 1 * ((n : ℝ) + 1)) * dist z z') := by
  -- The `y`-coordinates of the pullback are untouched: its slices are slices of `F` at `ψ l x`.
  have hslice : ∀ (i : Fin k) (l : Fin p → ℝ) (x : ℝ),
      Work.WilkG4c.slice (fun z : Fin (n + 1) → ℝ => F i l (Fin.cons (ψ l (z 0)) (Fin.tail z))) x
        = Work.WilkG4c.slice (F i l) (ψ l x) := by
    intro i l x
    funext y
    simp [Work.WilkG4c.slice, Work.WilkG4c.pt]
  constructor
  · -- `PY` transfers to the pullback, `ψ l` mapping `I` into the cell interval `(u,v)`.
    intro i l hl x hx m hm y hy
    rw [hslice i l x]
    exact hY i l hl (ψ l x) (hψI l hl x hx) m hm y hy
  · -- The Lipschitz bound, by the two-step mean value inequality.
    intro i l hl z z' hz hz'
    -- The cell interval is non-degenerate, as `ψ l` maps the non-empty `I` into `(u,v)`.
    have hs : (1 / 2 : ℝ) ∈ Work.WilkG4c.I := ⟨by norm_num, by norm_num⟩
    obtain ⟨hu1, hu2⟩ := hψI l hl (1 / 2) hs
    have huv : u < v := lt_trans hu1 hu2
    have hβl : 0 < β l := hβ l hl
    -- Membership facts for the two cube points.
    have hz0 : z 0 ∈ Work.WilkG4c.I := hz 0
    have hz0' : z' 0 ∈ Work.WilkG4c.I := hz' 0
    have htz : Fin.tail z ∈ WilkiesDesign.openCube n := fun j => hz j.succ
    have htz' : Fin.tail z' ∈ WilkiesDesign.openCube n := fun j => hz' j.succ
    have hψz : ψ l (z 0) ∈ Set.Ioo u v := hψI l hl (z 0) hz0
    have hψz' : ψ l (z' 0) ∈ Set.Ioo u v := hψI l hl (z' 0) hz0'
    -- The `x`-derivative bound on the cell: `Work.WilkG4c.PullXLipOn`.
    have hxbd : ∀ x ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n,
        |Work.WilkG4c.xDeriv (F i) l x y| * β l ≤ 2 * ((n : ℝ) + 1) :=
      Work.WilG4c.PullXLipOn (F i) (γ i) β l u v huv hβl
        (fun x hx => hγc i l hl x hx)
        (fun x hx y hy => hC1 i l hl x hx y hy)
        (fun x hx y hy j => hyb i l hl x hx y hy j)
        (fun x hx y hy => hmax i l hl x hx y hy)
        (fun j => hγC1 i l hl j)
        (fun x hx j => hγb i l hl x hx j)
        (fun x hx => hcb i l hl x hx)
        (hcC1 i l hl)
    -- The three Lipschitz inputs.
    have hYlip := Work.WilkG4c.SliceLipInY (F i) l (ψ l (z 0))
        (fun y hy => hC1 i l hl (ψ l (z 0)) hψz y hy)
        (fun y hy j => hyb i l hl (ψ l (z 0)) hψz y hy j)
    have hXlip := Work.WilkG4c.SliceLipInX (F i) l u v (β l) hβl
        (fun x hx y hy => hC1 i l hl x hx y hy) hxbd
    have hψlip := Work.WilG4c.PsiLipOnI ψ l (β l) (hψC1 l hl) (hψb l hl)
    -- The `y`-step, the `x`-step, and the `ψ`-step.
    have h1 : |F i l (Work.WilkG4c.pt (ψ l (z 0)) (Fin.tail z))
        - F i l (Work.WilkG4c.pt (ψ l (z 0)) (Fin.tail z'))|
        ≤ (n : ℝ) * dist (Fin.tail z) (Fin.tail z') :=
      hYlip (Fin.tail z) htz (Fin.tail z') htz'
    have h2 : |F i l (Work.WilkG4c.pt (ψ l (z 0)) (Fin.tail z'))
        - F i l (Work.WilkG4c.pt (ψ l (z' 0)) (Fin.tail z'))|
        ≤ (2 * ((n : ℝ) + 1) / β l) * |ψ l (z 0) - ψ l (z' 0)| :=
      hXlip (ψ l (z 0)) hψz (ψ l (z' 0)) hψz' (Fin.tail z') htz'
    have h3 : |ψ l (z 0) - ψ l (z' 0)| ≤ β l * |z 0 - z' 0| := hψlip (z 0) hz0 (z' 0) hz0'
    -- Coordinatewise bounds on the two `dist` factors of the cube metric.
    have htail : dist (Fin.tail z) (Fin.tail z') ≤ dist z z' := by
      rw [dist_pi_le_iff dist_nonneg]
      intro j
      exact dist_le_pi_dist z z' j.succ
    have h0 : |z 0 - z' 0| ≤ dist z z' := by
      have h := dist_le_pi_dist z z' (0 : Fin (n + 1))
      rwa [Real.dist_eq] at h
    -- The `β l` of the parametrisation cancels against the `1/β l` of the `x`-step.
    have hkey : (2 * ((n : ℝ) + 1) / β l) * (β l * |z 0 - z' 0|)
        = 2 * ((n : ℝ) + 1) * |z 0 - z' 0| := by
      field_simp
    have hnn : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) / β l :=
      div_nonneg (by positivity) (le_of_lt hβl)
    calc |F i l (Fin.cons (ψ l (z 0)) (Fin.tail z)) - F i l (Fin.cons (ψ l (z' 0)) (Fin.tail z'))|
        = |F i l (Work.WilkG4c.pt (ψ l (z 0)) (Fin.tail z))
            - F i l (Work.WilkG4c.pt (ψ l (z' 0)) (Fin.tail z'))| := rfl
      _ ≤ |F i l (Work.WilkG4c.pt (ψ l (z 0)) (Fin.tail z))
              - F i l (Work.WilkG4c.pt (ψ l (z 0)) (Fin.tail z'))|
            + |F i l (Work.WilkG4c.pt (ψ l (z 0)) (Fin.tail z'))
                - F i l (Work.WilkG4c.pt (ψ l (z' 0)) (Fin.tail z'))| := abs_sub_le _ _ _
      _ ≤ (n : ℝ) * dist (Fin.tail z) (Fin.tail z')
            + (2 * ((n : ℝ) + 1) / β l) * |ψ l (z 0) - ψ l (z' 0)| := add_le_add h1 h2
      _ ≤ (n : ℝ) * dist (Fin.tail z) (Fin.tail z')
            + (2 * ((n : ℝ) + 1) / β l) * (β l * |z 0 - z' 0|) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 hnn)
      _ = (n : ℝ) * dist (Fin.tail z) (Fin.tail z')
            + 2 * ((n : ℝ) + 1) * |z 0 - z' 0| := by rw [hkey]
      _ ≤ ((n : ℝ) + 2 * ((n : ℝ) + 1)) * dist z z' := by
          have h1' : (n : ℝ) * dist (Fin.tail z) (Fin.tail z') ≤ (n : ℝ) * dist z z' :=
            mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg n)
          have h2' : 2 * ((n : ℝ) + 1) * |z 0 - z' 0| ≤ 2 * ((n : ℝ) + 1) * dist z z' :=
            mul_le_mul_of_nonneg_left h0 (by positivity)
          linarith
      _ ≤ (max (2 * ((n : ℝ) + 1)) 1 * ((n : ℝ) + 1)) * dist z z' := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          have hmul := mul_le_mul_of_nonneg_right (le_max_left (2 * ((n : ℝ) + 1)) 1)
            (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [mul_nonneg hn hn]

end Work.WilG4c
