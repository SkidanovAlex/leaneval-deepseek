/-
  WilG4c — the covering step of the per-cell engine (BNZ §5.5).

  Given the base parametrisation `χ` of the cell `κ` (surjective onto the fibre of `κ`, cube
  valued), the two fibre ends `lo, hi`, the `n`-cube charts `Ψ_ih` of the inductive hypothesis
  (with the `ε/4`-approximation data `hψ`), and the grid data `lam, Kg`, the rescaled per-cell
  charts `engFinset χ lo hi Ψ_ih lam Kg` cover the fibre of `κ` over `Λ` up to `ε`.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.EngineDefs
import Submission.Work.WilG4c.FibreEndsInterval
import Submission.Work.WilG4c.tileN

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- The grid point `v_k := min (k/2) (lam - 1)` used in the tiling of the cube. -/
def gridPt {N K : ℕ} (lam : ℝ) (k : Fin N → Fin K) : Fin N → ℝ :=
  fun i => min (((k i : ℕ) : ℝ) / 2) (lam - 1)

/-- The pointwise bounds of the grid point: `0 ≤ v_k i ≤ lam - 1`. -/
theorem gridPt_bounds {N K : ℕ} (lam : ℝ) (hlam : 1 ≤ lam) (k : Fin N → Fin K) :
    ∀ i, 0 ≤ gridPt lam k i ∧ gridPt lam k i ≤ lam - 1 := by
  intro i
  exact ⟨le_min (by positivity) (by linarith), min_le_right _ _⟩

/-- The open cube of `ℝ^N` is open. -/
theorem isOpen_openCube_engine (N : ℕ) : IsOpen (openCube N) := by
  have h : openCube N = Set.pi Set.univ (fun _ : Fin N => Set.Ioo (0 : ℝ) 1) := by
    ext t
    simp [openCube]
  rw [h]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

/-- `Fin.init` commutes with `Fin.append` (local copy, to avoid importing `StepCellAux1`). -/
theorem engInit_append {p N : ℕ} (l : Fin p → ℝ) (y : Fin (N + 1) → ℝ) :
    Fin.init (Fin.append (n := N + 1) l y) = Fin.append l (Fin.init y) := by
  have h : (Fin.snoc (Fin.append l (Fin.init y)) (y (Fin.last N)) : Fin (p + N + 1) → ℝ)
      = Fin.append (n := N + 1) l y := by
    rw [← Fin.append_snoc l (Fin.init y) (y (Fin.last N)), Fin.snoc_init_self]
  rw [← h, Fin.init_snoc]

/-- `Fin.init '' A` is the projection `projLast A` (local copy). -/
theorem engInit_image_projLast {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) :
    Fin.init '' A = projLast A := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z (Fin.last n), by rw [Fin.snoc_init_self]; exact hz⟩
  · rintro ⟨t, ht⟩
    refine ⟨Fin.snoc x t, ht, ?_⟩
    simp

/-- The chart of the per-cell engine attached to an `n`-cube chart `ψ` and a grid point `k`:
`(l, y) ↦ cellChart χ M W ψ l ((v_k + y)/lam)`. -/
def engChart {p n K : ℕ} (χ ψ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (M W : (Fin p → ℝ) → (Fin n → ℝ) → ℝ) (lam : ℝ) (k : Fin (n + 1) → Fin K) :
    WilkG4c.ChartTuple p (n + 1) :=
  fun j l y => cellChart χ M W ψ l (fun i => (gridPt lam k i + y i) / lam) j

/-- The `Finset` of all rescaled per-cell charts: all `n`-cube charts of `Ψ_ih`, translated by
all grid points of the net `{0, 1/2, …, lam - 1}^{n+1}` and rescaled by `lam`. -/
def engFinset {p n : ℕ} (χ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (lo hi : (Fin (p + n) → ℝ) → ℝ) (Ψ_ih : Finset (WilkG4c.ChartTuple p n)) (lam : ℝ)
    (Kg : ℕ) : Finset (WilkG4c.ChartTuple p (n + 1)) :=
  (Ψ_ih.product (Finset.univ : Finset (Fin (n + 1) → Fin Kg))).image
    (fun q : WilkG4c.ChartTuple p n × (Fin (n + 1) → Fin Kg) =>
      engChart χ (fun l u => fun j => q.1 j l u) (midFun lo hi χ) (widFun lo hi χ) lam q.2)

/-- The coordinates `≠ Fin.last` of the cell chart. -/
theorem cellChart_castSucc {p n : ℕ} (χ ψ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (M W : (Fin p → ℝ) → (Fin n → ℝ) → ℝ) (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ)
    (j : Fin n) :
    cellChart χ M W ψ l z (Fin.castSucc j) = χ l (ψ l (Fin.init z)) j := by
  have h : ¬ ((Fin.castSucc j : Fin (n + 1)) : ℕ) = n := by
    have h1 : ((Fin.castSucc j : Fin (n + 1)) : ℕ) = (j : ℕ) := rfl
    rw [h1]
    exact Nat.ne_of_lt j.isLt
  unfold cellChart
  rw [dif_neg h]
  exact congrArg (χ l (ψ l (Fin.init z))) (Fin.ext rfl)

/-- The last coordinate of the cell chart. -/
theorem cellChart_last {p n : ℕ} (χ ψ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (M W : (Fin p → ℝ) → (Fin n → ℝ) → ℝ) (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) :
    cellChart χ M W ψ l z (Fin.last n)
      = M l (ψ l (Fin.init z)) + (z (Fin.last n) - 1 / 2) *
        (2 * W l (ψ l (Fin.init z)) - 1 / 2) := by
  have h : ((Fin.last n : Fin (n + 1)) : ℕ) = n := rfl
  unfold cellChart
  rw [dif_pos h]

/-- **The covering step of the per-cell engine.**  Let `χ` parametrise the fibre of `κ`, `lo`,
`hi` be its two fibre ends, and `Ψ_ih` be `n`-cube charts approximating the parametrisation up
to `ε/4` (`hψ`).  Then the rescaled charts `engFinset χ lo hi Ψ_ih lam Kg` cover the fibre of
`κ` over `Λ` up to `ε`. -/
theorem engineCover (n p k : ℕ) (Λ : Set (Fin p → ℝ))
    (κ : Set (Fin (p + (n + 1)) → ℝ))
    (χ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (lo hi : (Fin (p + n) → ℝ) → ℝ)
    (Ψ_ih : Finset (WilkG4c.ChartTuple p n)) (lam : ℝ) (Kg : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hlam1 : 1 ≤ lam)
    (hKg : 2 * (lam - 1) + 2 ≤ (Kg : ℝ))
    (hκcell : IsCell (p + (n + 1)) κ)
    (hκI : ∀ z ∈ κ, z (Fin.last (p + n)) ∈ Set.Ioo (0 : ℝ) 1)
    (hlo : ∀ l : Fin (p + n) → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ κ) →
      (∀ x : ℝ, Fin.snoc l x ∈ κ → lo l ≤ x ∧ x ≤ hi l) ∧
      (∀ u : ℝ, lo l < u → ∃ x : ℝ, Fin.snoc l x ∈ κ ∧ x < u) ∧
      (∀ u : ℝ, u < hi l → ∃ x : ℝ, Fin.snoc l x ∈ κ ∧ u < x))
    (hχsurj : ∀ l ∈ Λ, ∀ y : Fin n → ℝ, Fin.append l y ∈ Fin.init '' κ →
      ∃ t ∈ openCube n, χ l t = y)
    (hψ : ∀ l ∈ Λ, ∀ t ∈ openCube n, ∃ ψ ∈ Ψ_ih, ∃ t' ∈ openCube n,
      ((fun j => ψ j l t') ∈ openCube n) ∧
      (∀ j : Fin n, |χ l (fun j' => ψ j' l t') j - χ l t j| < ε / 4) ∧
      |midFun lo hi χ l (fun j' => ψ j' l t') - midFun lo hi χ l t| < ε / 4 ∧
      |widFun lo hi χ l (fun j' => ψ j' l t') - widFun lo hi χ l t| < ε / 4) :
    ∀ l ∈ Λ, ∀ y : Fin (n + 1) → ℝ, Fin.append l y ∈ κ →
      ∃ φ ∈ engFinset χ lo hi Ψ_ih lam Kg, ∃ t ∈ openCube (n + 1),
        ∀ j : Fin (n + 1), |φ j l t - y j| < ε := by
  intro l hl y hy
  set x₀ : Fin n → ℝ := Fin.init y with hx₀
  have hxy : ∀ j : Fin n, x₀ j = y (Fin.castSucc j) := by
    intro j
    rw [hx₀, Fin.init_def]
  have hbase₀ : Fin.append l x₀ ∈ Fin.init '' κ := by
    rw [engInit_image_projLast]
    refine ⟨y (Fin.last n), ?_⟩
    have h1 : Fin.snoc (Fin.append l x₀) (y (Fin.last n)) = Fin.append l y := by
      rw [hx₀, ← Fin.append_snoc, Fin.snoc_init_self]
    rw [h1]; exact hy
  obtain ⟨t₀, ht₀, hχt₀⟩ := hχsurj l hl x₀ hbase₀
  obtain ⟨ψ, hψmem, t', ht', hψcube, hbj, hM4, hW4⟩ := hψ l hl t₀ ht₀
  set ψp : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) := fun l u => fun j => ψ j l u with hψp
  -- the fibre ends at the base point of the chart
  set w : Fin (p + n) → ℝ := Fin.append l x₀ with hw
  have hyw : Fin.snoc w (y (Fin.last n)) ∈ κ := by
    have h1 : Fin.snoc w (y (Fin.last n)) = Fin.append l y := by
      rw [hw, hx₀, ← Fin.append_snoc, Fin.snoc_init_self]
    rw [h1]; exact hy
  obtain ⟨hlo0, hlo1, hhi0, hhi1, hmid0, hmid1, hwid0, hwid1, hIoo, hsweep⟩ :=
    FibreEndsInterval κ hκcell hκI lo hi hlo w ⟨y (Fin.last n), hyw⟩
  obtain ⟨hylo, hyhi⟩ := (hlo w ⟨y (Fin.last n), hyw⟩).1 (y (Fin.last n)) hyw
  -- the midpoint and width of the fibre over the base point
  have hMt₀ : midFun lo hi χ l t₀ = (lo w + hi w) / 2 := by
    rw [hw]; simp only [midFun]; rw [hχt₀]
  have hWt₀ : 2 * widFun lo hi χ l t₀ - 1 / 2 = hi w - lo w := by
    rw [hw]; simp only [widFun]; rw [hχt₀]; ring
  -- the last coordinate of the target
  set τ : ℝ := if lo w < hi w then (y (Fin.last n) - lo w) / (hi w - lo w) else 1 / 2 with hτ
  have hτ0 : 0 ≤ τ := by
    rw [hτ]; split_ifs with hlt
    · exact div_nonneg (by linarith) (by linarith)
    · norm_num
  have hτ1 : τ ≤ 1 := by
    rw [hτ]; split_ifs with hlt
    · rw [div_le_one (by linarith)]
      linarith
    · norm_num
  have hmidτ : midFun lo hi χ l t₀ + (τ - 1 / 2) * (2 * widFun lo hi χ l t₀ - 1 / 2)
      = y (Fin.last n) := by
    rw [hMt₀, hWt₀, hτ]
    split_ifs with hlt
    · have hne : hi w - lo w ≠ 0 := by linarith
      field_simp
      ring_nf
    · have hhi : hi w = lo w := by
        have h0 : hi w - lo w = 0 := le_antisymm (by linarith [not_lt.mp hlt]) hwid0
        linarith
      have hy1 : y (Fin.last n) = lo w := le_antisymm (le_trans hyhi (not_lt.mp hlt)) hylo
      rw [hhi, hy1]; ring
  -- an interior last coordinate
  set ζ : ℝ := (1 - ε / 8) * τ + (ε / 8) * (1 / 2) with hζ
  have hζI : ζ ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Set.mem_Ioo, hζ]
    constructor
    · nlinarith [hτ0, hε0, hε1]
    · nlinarith [hτ1, hε0, hε1]
  have hζτ : |ζ - τ| ≤ ε / 8 := by
    have h2 : ζ - τ = -((ε / 8) * (τ - 1 / 2)) := by rw [hζ]; ring
    rw [h2, abs_neg, abs_mul, abs_of_pos (by linarith [hε0] : (0 : ℝ) < ε / 8)]
    have h3 : |τ - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    calc (ε / 8) * |τ - 1 / 2| ≤ (ε / 8) * (1 / 2) :=
          mul_le_mul_of_nonneg_left h3 (by linarith [hε0])
      _ ≤ ε / 8 := by linarith [hε0]
  -- the point `(t', ζ)` is in the cube
  have htz : Fin.snoc t' ζ ∈ openCube (n + 1) := by
    intro j
    by_cases hjn : (j : ℕ) = n
    · have hjl : j = Fin.last n := Fin.ext hjn
      subst hjl
      rw [Fin.snoc_last]
      exact hζI
    · have hlt : (j : ℕ) < n := by have := j.isLt; omega
      have hcast : j = Fin.castSucc (⟨(j : ℕ), hlt⟩ : Fin n) := Fin.ext rfl
      rw [hcast, Fin.snoc_castSucc]
      exact ht' ⟨(j : ℕ), hlt⟩
  -- the grid point covering `(t', ζ)`
  obtain ⟨kk, yt, hytcube, hkbd, htile⟩ := tileN (n + 1) lam hlam1 Kg hKg (Fin.snoc t' ζ) htz
  refine ⟨engChart χ ψp (midFun lo hi χ) (widFun lo hi χ) lam kk, ?_, yt, hytcube, ?_⟩
  · rw [engFinset]
    refine Finset.mem_image.mpr ⟨(ψ, kk), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨hψmem, Finset.mem_univ _⟩
  · have hzarg : (fun i : Fin (n + 1) => (gridPt lam kk i + yt i) / lam) = Fin.snoc t' ζ := by
      funext i
      simpa only [gridPt] using htile i
    intro j
    have hval : engChart χ ψp (midFun lo hi χ) (widFun lo hi χ) lam kk j l yt
        = cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l (Fin.snoc t' ζ) j := by
      show cellChart χ (midFun lo hi χ) (widFun lo hi χ) ψp l
        (fun i => (gridPt lam kk i + yt i) / lam) j = _
      rw [hzarg]
    rw [hval]
    by_cases hjn : (j : ℕ) = n
    · -- the last coordinate
      have hjl : j = Fin.last n := Fin.ext hjn
      subst hjl
      rw [cellChart_last, Fin.init_snoc, Fin.snoc_last]
      -- the last coordinate of the target
      have h2B : |2 * widFun lo hi χ l t₀ - 1 / 2| ≤ 1 := by
        rw [hWt₀, abs_le]; constructor <;> linarith [hwid0, hwid1]
      have hzeta : |ζ - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> linarith [hζI.1, hζI.2]
      have hkey : midFun lo hi χ l (fun j' => ψ j' l t')
            + (ζ - 1 / 2) * (2 * widFun lo hi χ l (fun j' => ψ j' l t') - 1 / 2)
            - y (Fin.last n)
          = (midFun lo hi χ l (fun j' => ψ j' l t') - midFun lo hi χ l t₀)
            + (ζ - 1 / 2) * ((2 * widFun lo hi χ l (fun j' => ψ j' l t') - 1 / 2)
              - (2 * widFun lo hi χ l t₀ - 1 / 2))
            + (ζ - τ) * (2 * widFun lo hi χ l t₀ - 1 / 2) := by
        rw [← hmidτ]; ring
      rw [hkey]
      set X := midFun lo hi χ l (fun j' => ψ j' l t') - midFun lo hi χ l t₀ with hX
      set Y := (ζ - 1 / 2) * ((2 * widFun lo hi χ l (fun j' => ψ j' l t') - 1 / 2)
        - (2 * widFun lo hi χ l t₀ - 1 / 2)) with hY
      set Z := (ζ - τ) * (2 * widFun lo hi χ l t₀ - 1 / 2) with hZ
      have h1 : |X| ≤ ε / 4 := le_of_lt hM4
      have h2 : |Y| ≤ (1 / 2) * (ε / 2) := by
        rw [hY, abs_mul]
        have hY2 : |(2 * widFun lo hi χ l (fun j' => ψ j' l t') - 1 / 2)
            - (2 * widFun lo hi χ l t₀ - 1 / 2)|
            = 2 * |widFun lo hi χ l (fun j' => ψ j' l t') - widFun lo hi χ l t₀| := by
          rw [show (2 * widFun lo hi χ l (fun j' => ψ j' l t') - 1 / 2)
              - (2 * widFun lo hi χ l t₀ - 1 / 2)
              = 2 * (widFun lo hi χ l (fun j' => ψ j' l t') - widFun lo hi χ l t₀) by ring,
            abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        rw [hY2]
        calc |ζ - 1 / 2| * (2 * |widFun lo hi χ l (fun j' => ψ j' l t')
              - widFun lo hi χ l t₀|)
            = (|ζ - 1 / 2| * 2) * |widFun lo hi χ l (fun j' => ψ j' l t')
              - widFun lo hi χ l t₀| := by ring
          _ ≤ (1 / 2 * 2) * (ε / 4) :=
              mul_le_mul (mul_le_mul hzeta le_rfl (by norm_num) (by norm_num))
                (le_of_lt hW4) (abs_nonneg _) (by norm_num)
          _ = (1 / 2) * (ε / 2) := by ring
      have h3 : |Z| ≤ (ε / 8) * 1 := by
        rw [hZ, abs_mul]
        exact mul_le_mul hζτ h2B (abs_nonneg _) (by linarith [hε0])
      have ht1 : |X + Y + Z| ≤ |X + Y| + |Z| := abs_add_le (X + Y) Z
      have ht2 : |X + Y| ≤ |X| + |Y| := abs_add_le X Y
      linarith [ht1, ht2, h1, h2, h3, hε0, hε1]
    · -- a non-last coordinate
      have hlt : (j : ℕ) < n := by have := j.isLt; omega
      have hjl : j = Fin.castSucc (⟨(j : ℕ), hlt⟩ : Fin n) := Fin.ext rfl
      rw [hjl, cellChart_castSucc, Fin.init_snoc, ← hxy ⟨(j : ℕ), hlt⟩,
        ← congrFun hχt₀ ⟨(j : ℕ), hlt⟩]
      linarith [hbj ⟨(j : ℕ), hlt⟩, hε0]

end Work.WilG4c
