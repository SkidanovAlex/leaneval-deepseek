/-
  WilC4/ErealDefs : the *real-scale* cluster exponent set of the ULPM route, and its
  relation to the (natural-scale) `Route.ClusterE` of `Submission/Work/WilC4/ULPMRoute.lean`.

  `Route.ClusterE Y B₀` quantifies over *natural* scales `B ≥ 1`:
  `ρ ∈ ClusterE` iff for every `B : ℕ`, `0 < B`, there are `c, x` with `x > 0`, `x` `B`-deep and
  the ratio `f_c(2t)/f_c(t)` within `1/B` of `ρ` on the whole window `[x/B, xB]`.

  For the finiteness proof it is convenient to work with *real* scales.  `ClusterER Y B₀` is the
  same condition with `β : ℝ`, `0 < β` in place of `B : ℕ`.  The key structural fact is
  `ClusterE Y B₀ ⊆ ClusterER Y B₀`: deepness at scale `N` implies deepness at every smaller scale
  `β ≤ N` (the forbidden interval `[x/(2β), 2βx]` is contained in `[x/(2N), 2Nx]`), and the window
  `[x/β, βx]` is contained in `[x/N, Nx]` while the tolerance `1/β` is *larger* than `1/N`.

  `ClusterER` is `∅`-definable (that is the point of using real scales, see the delegated
  `ClusterER_definable`), and `ClusterER` finite implies `ClusterE` finite.
-/
import Mathlib
import Submission.Work.WilC4.ULPMRoute

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-- Deepness at a *real* scale `β`: the multiplicative interval `[x/(2β), 2βx]` misses every
breakpoint of the fibre `B₀` at the parameter `c`.  This is `Route.IsDeep` with `β : ℝ`. -/
def IsDeepR (B₀ : Set (Fin (k + 1) → ℝ)) (c : Fin k → ℝ) (β x : ℝ) : Prop :=
  ∀ b : ℝ, Fin.cons b c ∈ B₀ → ¬ (x / (2 * β) ≤ b ∧ b ≤ 2 * β * x)

/-- A `β`-witness for the cluster value `ρ`: a positive base point `x` at which the fibre function
is deep, and such that the doubling ratio `f_c(2t)/f_c(t)` is within `1/β` of `ρ` on the whole
window `[x/β, xβ]`. -/
def IsWit (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) (ρ β : ℝ)
    (c : Fin k → ℝ) (x : ℝ) : Prop :=
  0 < x ∧ IsDeepR B₀ c β x ∧
    ∀ t : ℝ, x / β ≤ t → t ≤ x * β →
      ∀ y y' : ℝ, Route.Gr Y c t y → Route.Gr Y c (2 * t) y' → y ≠ 0 →
        |y' / y - ρ| ≤ 1 / β

/-- **The real-scale cluster exponent set.**  `ρ` is in `ClusterER Y B₀` iff for every real scale
`β > 0` there is a `β`-witness for `ρ`. -/
def ClusterER (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Set ℝ :=
  {ρ | ∀ β : ℝ, 0 < β → ∃ (c : Fin k → ℝ) (x : ℝ), IsWit Y B₀ ρ β c x}

theorem mem_ClusterER {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)} {ρ : ℝ} :
    ρ ∈ ClusterER Y B₀ ↔ ∀ β : ℝ, 0 < β → ∃ (c : Fin k → ℝ) (x : ℝ), IsWit Y B₀ ρ β c x :=
  Iff.rfl

/-! ## Monotonicity of witnesses in the scale -/

/-- Deepness at a smaller scale follows from deepness at a larger one (the forbidden interval is
contained in the larger one). -/
theorem IsDeepR.mono {B₀ : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {β β' x : ℝ}
    (h : IsDeepR B₀ c β x) (hβ' : 0 < β') (hββ' : β' ≤ β) (hx : 0 < x) : IsDeepR B₀ c β' x := by
  intro b hb hb'
  refine h b hb ⟨?_, ?_⟩
  · have h2β : 0 < 2 * β' := by linarith
    have hle : 2 * β' ≤ 2 * β := by linarith
    have hmono : x / (2 * β) ≤ x / (2 * β') :=
      div_le_div_of_nonneg_left (le_of_lt hx) h2β hle
    linarith [hb'.1]
  · have hβ0 : 0 < β := lt_of_lt_of_le hβ' hββ'
    have : 2 * β' * x ≤ 2 * β * x := by nlinarith
    linarith [hb'.2]

/-- A `β`-witness is a `β'`-witness for every smaller positive scale. -/
theorem IsWit.mono {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)} {ρ β β' : ℝ}
    {c : Fin k → ℝ} {x : ℝ} (h : IsWit Y B₀ ρ β c x) (hβ' : 0 < β') (hββ' : β' ≤ β) :
    IsWit Y B₀ ρ β' c x := by
  obtain ⟨hx, hdeep, hrat⟩ := h
  refine ⟨hx, hdeep.mono hβ' hββ' hx, ?_⟩
  intro t ht1 ht2 y y' hy hy' hy0
  have hβ0 : 0 < β := lt_of_lt_of_le hβ' hββ'
  have ht1' : x / β ≤ t := by
    have hmono : x / β ≤ x / β' := div_le_div_of_nonneg_left (le_of_lt hx) hβ' hββ'
    linarith [ht1]
  have ht2' : t ≤ x * β := le_trans ht2 (by nlinarith)
  have hb := hrat t ht1' ht2' y y' hy hy' hy0
  have hle : 1 / β ≤ 1 / β' := one_div_le_one_div_of_le hβ' hββ'
  linarith [hb]

/-! ## The real-scale cluster set contains the natural-scale one -/

/-- **`Route.ClusterE ⊆ ClusterER`.**  Deepness at scale `N` implies deepness at every smaller
scale, and the window shrinks while the tolerance grows, so a natural-scale witness is a
real-scale witness. -/
theorem ClusterE_subset_ClusterER (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) :
    Route.ClusterE Y B₀ ⊆ ClusterER Y B₀ := by
  intro ρ hρ β hβ
  obtain ⟨N : ℕ, hN⟩ : ∃ N : ℕ, max 1 β ≤ (N : ℝ) := exists_nat_ge (max 1 β)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
    exact_mod_cast this
  have hβN : β ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  obtain ⟨c, x, hx, hdeep, hrat⟩ := hρ N hN1
  refine ⟨c, x, IsWit.mono (Y := Y) (B₀ := B₀) (β := (N : ℝ)) (β' := β) ⟨hx, hdeep, hrat⟩ hβ
    hβN⟩

/-! ## The candidate values and the diagonal graph -/

/-- The set of *candidate values* at the scale `β` for the cluster value `ρ`: all numbers
`f_c(xβ)/f_c(x)` where `(c,x)` is a `β`-witness for `ρ`.  Written with `Route.Gr` (no division):
`y * u = v` with `u` the value at `x` and `v` the value at `xβ`. -/
def Cand (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) (ρ β : ℝ) : Set ℝ :=
  {y | ∃ (c : Fin k → ℝ) (x : ℝ), IsWit Y B₀ ρ β c x ∧
      ∃ u v : ℝ, Route.Gr Y c x u ∧ Route.Gr Y c (x * β) v ∧ y * u = v}

/-- The *diagonal graph*: at the scale `β ≥ R` the unique point `y` which is the infimum of the
candidate values `Cand Y B₀ ρ β`.  `inf` is written in first-order form (`y` is a lower bound and
is approximated from above). -/
def Diag (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) (ρ R : ℝ) :
    Set (Fin 2 → ℝ) :=
  {v | R ≤ v 0 ∧ (∀ y ∈ Cand Y B₀ ρ (v 0), v 1 ≤ y) ∧
    (∀ ε : ℝ, 0 < ε → ∃ y ∈ Cand Y B₀ ρ (v 0), y < v 1 + ε)}

/-! ## The niceness of the fibre off the breakpoints

`hgood` instantiated on the deep interval `(x/(2β), 2βx)` gives uniqueness, nonvanishing and
continuity of the fibre function there; continuity and nonvanishing give constant sign. -/

/-- The "good fibre" hypothesis (the `hgood` of `ulpm_E_finite`): on every interval avoiding
`B₀`, the fibre is a function, it is nowhere zero, and it is continuous. -/
def GoodFibre (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Prop :=
  ∀ (c : Fin k → ℝ) (a b : ℝ), a < b → (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) →
    (∀ x ∈ Set.Ioo a b, ∃! y : ℝ, Route.Gr Y c x y) ∧
    (∀ x ∈ Set.Ioo a b, ∀ y : ℝ, Route.Gr Y c x y → y ≠ 0) ∧
    (∀ x ∈ Set.Ioo a b, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b,
      ∀ y y' : ℝ, |x' - x| < δ → Route.Gr Y c x y →
      Route.Gr Y c x' y' → |y' - y| < ε)

/-- The points of the deep interval avoid the breakpoint family `B₀`. -/
theorem deep_free {B₀ : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {β x : ℝ}
    (hdeep : IsDeepR B₀ c β x) :
    ∀ z ∈ Set.Ioo (x / (2 * β)) (2 * β * x), Fin.cons z c ∉ B₀ := by
  intro z hz hzB
  exact hdeep z hzB ⟨le_of_lt hz.1, le_of_lt hz.2⟩

/-- `hgood` on the deep interval. -/
theorem deep_nice {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)} (hgood : GoodFibre Y B₀)
    {c : Fin k → ℝ} {β x : ℝ} (hβ : 1 ≤ β) (hx : 0 < x) (hdeep : IsDeepR B₀ c β x) :
    (∀ z ∈ Set.Ioo (x / (2 * β)) (2 * β * x), ∃! y : ℝ, Route.Gr Y c z y) ∧
    (∀ z ∈ Set.Ioo (x / (2 * β)) (2 * β * x), ∀ y : ℝ, Route.Gr Y c z y → y ≠ 0) ∧
    (∀ z ∈ Set.Ioo (x / (2 * β)) (2 * β * x), ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z' ∈ Set.Ioo (x / (2 * β)) (2 * β * x), ∀ y y' : ℝ, |z' - z| < δ →
        Route.Gr Y c z y → Route.Gr Y c z' y' → |y' - y| < ε) := by
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ
  have hab : x / (2 * β) < 2 * β * x := by
    have h2 : 1 < 4 * β ^ 2 := by nlinarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  exact hgood c _ _ hab (deep_free hdeep)

/-- The value `valY Y c z` at a point of the deep interval is a genuine value there, and it is
non-zero. -/
theorem deep_val {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)} (hgood : GoodFibre Y B₀)
    {c : Fin k → ℝ} {β x : ℝ} (hβ : 1 ≤ β) (hx : 0 < x) (hdeep : IsDeepR B₀ c β x)
    {z : ℝ} (hz : z ∈ Set.Ioo (x / (2 * β)) (2 * β * x)) :
    Route.Gr Y c z (Route.valY Y c z) ∧ Route.valY Y c z ≠ 0 := by
  obtain ⟨hu, hnz, -⟩ := deep_nice hgood hβ hx hdeep
  have hInD : Route.InD Y c z := ((hu z hz).exists).imp fun y hy => hy
  exact ⟨Route.valY_mem Y c z hInD, hnz z hz _ (Route.valY_mem Y c z hInD)⟩

/-- The fibre function `valY Y c` is continuous on the deep interval. -/
theorem deep_cont {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)} (hgood : GoodFibre Y B₀)
    {c : Fin k → ℝ} {β x : ℝ} (hβ : 1 ≤ β) (hx : 0 < x) (hdeep : IsDeepR B₀ c β x) :
    ContinuousOn (fun t => Route.valY Y c t) (Set.Ioo (x / (2 * β)) (2 * β * x)) := by
  obtain ⟨hu, hnz, hcont⟩ := deep_nice hgood hβ hx hdeep
  rw [Metric.continuousOn_iff]
  intro z hz ε hε
  obtain ⟨δ, hδ0, hδ⟩ := hcont z hz ε hε
  refine ⟨δ, hδ0, fun z' hz' hdist => ?_⟩
  have hInDz : Route.InD Y c z := ((hu z hz).exists).imp fun y hy => hy
  have hInDz' : Route.InD Y c z' := ((hu z' hz').exists).imp fun y hy => hy
  have h := hδ z' hz' _ _ (by simpa [Real.dist_eq] using hdist) (Route.valY_mem Y c z hInDz)
    (Route.valY_mem Y c z' hInDz')
  simpa [Real.dist_eq] using h

/-- On the deep interval the fibre function has constant sign: any two values there have positive
product. -/
theorem deep_sign {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)} (hgood : GoodFibre Y B₀)
    {c : Fin k → ℝ} {β x : ℝ} (hβ : 1 ≤ β) (hx : 0 < x) (hdeep : IsDeepR B₀ c β x)
    {s t : ℝ} (hs : s ∈ Set.Ioo (x / (2 * β)) (2 * β * x))
    (ht : t ∈ Set.Ioo (x / (2 * β)) (2 * β * x)) {u v : ℝ}
    (hu : Route.Gr Y c s u) (hv : Route.Gr Y c t v) : 0 < u * v := by
  obtain ⟨huq, hnz, hcont⟩ := deep_nice hgood hβ hx hdeep
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ
  have hab : x / (2 * β) < 2 * β * x := by
    have h2 : 1 < 4 * β ^ 2 := by nlinarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hI : IsPreconnected (Set.Ioo (x / (2 * β)) (2 * β * x)) := isPreconnected_Ioo
  have hS : IsPreconnected ((fun t => Route.valY Y c t) '' Set.Ioo (x / (2 * β)) (2 * β * x)) :=
    IsPreconnected.image hI (fun t => Route.valY Y c t) (deep_cont hgood hβ hx hdeep)
  have hOC := hS.ordConnected
  -- the two values are `valY`s
  have hus : u = Route.valY Y c s := (huq s hs).unique hu (Route.valY_mem Y c s ((huq s hs).exists.imp fun y hy => hy))
  have hvt : v = Route.valY Y c t := (huq t ht).unique hv (Route.valY_mem Y c t ((huq t ht).exists.imp fun y hy => hy))
  have hmem_s : Route.valY Y c s ∈ (fun t => Route.valY Y c t) '' Set.Ioo (x / (2 * β)) (2 * β * x) :=
    ⟨s, hs, rfl⟩
  have hmem_t : Route.valY Y c t ∈ (fun t => Route.valY Y c t) '' Set.Ioo (x / (2 * β)) (2 * β * x) :=
    ⟨t, ht, rfl⟩
  have hzero : (0 : ℝ) ∉ (fun t => Route.valY Y c t) '' Set.Ioo (x / (2 * β)) (2 * β * x) := by
    rintro ⟨z, hz, hz0⟩
    have : Route.valY Y c z ≠ 0 := (deep_val hgood hβ hx hdeep hz).2
    exact this hz0
  rw [hus, hvt]
  have hP : Route.valY Y c s ≠ 0 := (deep_val hgood hβ hx hdeep hs).2
  have hQ : Route.valY Y c t ≠ 0 := (deep_val hgood hβ hx hdeep ht).2
  rcases lt_or_gt_of_ne hP with hPs | hPs <;> rcases lt_or_gt_of_ne hQ with hQt | hQt
  · exact mul_pos_of_neg_of_neg hPs hQt
  · exfalso
    exact hzero (hOC.out hmem_s hmem_t ⟨le_of_lt hPs, le_of_lt hQt⟩)
  · exfalso
    exact hzero (hOC.out hmem_t hmem_s ⟨le_of_lt hQt, le_of_lt hPs⟩)
  · exact mul_pos hPs hQt

/-! ## O-minimality input (local copy, to avoid the `mono_real` import) -/

theorem oMin_structure_local (hOM : WilkiesDesign.CG.OMinModels) {X : Set (Fin 1 → ℝ)}
    (hX : (Set.univ : Set ℝ).Definable WilkiesDesign.CG.LRc X) :
    ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      X = {x : Fin 1 → ℝ | x 0 ∈ ⋃₀ (s : Set (Set ℝ))} := by
  haveI : ℝ ⊨ WilkiesDesign.CG.TR :=
    inferInstanceAs (ℝ ⊨ WilkiesDesign.CG.LRc.completeTheory ℝ)
  exact hOM ℝ X hX

/-- A `∅`-definable set of reals is a finite union of order-convex pieces. -/
theorem oMin_ordConnected_set_local (hOM : WilkiesDesign.CG.OMinModels) {S : Set ℝ}
    (hS : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc S) :
    ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧ S = ⋃₀ (s : Set (Set ℝ)) := by
  have h : (Set.univ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {x : Fin 1 → ℝ | x 0 ∈ S} := hS.mono (Set.empty_subset _)
  obtain ⟨s, hs, heq⟩ := oMin_structure_local hOM h
  refine ⟨s, hs, ?_⟩
  ext x
  have h' := Set.ext_iff.mp heq (fun _ : Fin 1 => x)
  simpa using h'

end Work.WilC4
