import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.pb_decay
import Submission.Work.WilC4.pb_poly_bound
import Submission.Work.WilC4.definable_isGLB_family

set_option linter.unusedVariables false

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

section BadScaleRate

variable {k : ℕ}

/-! ## The order structure of `BadScale`

`BadScale Y B E ε` decreases with `ε`: the deviation condition `ε < |w/ρ - 1|` becomes easier
for smaller `ε`.  Equivalently, the complement `{ε | M ∉ BadScale Y B E ε}` is *upward* closed
in `ε`.  This is the only structural fact about `BadScale` used below besides the pointwise
equivalence `hbiff`. -/

/-- `BadScale Y B E ε' ⊆ BadScale Y B E ε` for `ε ≤ ε'`. -/
lemma mem_badScale_mono (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ)) (E : Set ℝ)
    {ε ε' M : ℝ} (hε : ε ≤ ε') (hM : M ∈ BadScale Y B E ε') : M ∈ BadScale Y B E ε := by
  obtain ⟨hM0, c, x, w, hx, hdeep, hrat, hbad⟩ := hM
  exact ⟨hM0, c, x, w, hx, hdeep, hrat,
    fun ρ hρE hρ0 => lt_of_le_of_lt hε (hbad ρ hρE hρ0)⟩

/-- The complement of `BadScale` is upward closed in the tolerance. -/
lemma not_mem_badScale_mono (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ))
    (E : Set ℝ) {ε ε' M : ℝ} (hε : ε ≤ ε') (hM : M ∉ BadScale Y B E ε) :
    M ∉ BadScale Y B E ε' :=
  fun h => hM (mem_badScale_mono Y B E hε h)

/-! ## The definable "good tolerance" set and its greatest-lower-bound graph -/

/-- The set of pairs `(M, ε)` with `0 ≤ ε ≤ 1` and `M` *not* a bad scale at tolerance `ε`, i.e.
`DevBdd Y B E M ε` when `M > 0`.  Over a fixed scale `M` this is the initial segment of the
"good tolerances" capped at `1`. -/
def GoodSet (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ)) (E : Set ℝ) :
    Set (Fin 2 → ℝ) :=
  {v : Fin 2 → ℝ | v 0 ∈ BadScale Y B E (v 1)}ᶜ ∩ {v : Fin 2 → ℝ | 0 ≤ v 1} ∩
    {v : Fin 2 → ℝ | v 1 ≤ 1}

/-- The graph of the least good tolerance: at the scale `M` the value `y` is the infimum of the
good tolerances `ε ∈ [0,1]` (equivalently, the least upper bound for the deviations).  It is
`∅`-definable by `definable_isGLB_family`, applied to the `∅`-definable set `GoodSet`. -/
def GoodGraph (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ)) (E : Set ℝ) :
    Set (Fin 2 → ℝ) :=
  {u : Fin 2 → ℝ | IsGLB {t : ℝ | Fin.snoc (Fin.init u) t ∈ GoodSet Y B E} (u (Fin.last 1))}

lemma mem_goodSet (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ)) (E : Set ℝ)
    (M y : ℝ) :
    (![M, y] : Fin 2 → ℝ) ∈ GoodSet Y B E ↔ M ∉ BadScale Y B E y ∧ 0 ≤ y ∧ y ≤ 1 := by
  simp only [GoodSet, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

lemma mem_goodGraph_iff (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ))
    (E : Set ℝ) (M y : ℝ) :
    (![M, y] : Fin 2 → ℝ) ∈ GoodGraph Y B E ↔
      IsGLB {t : ℝ | (![M, t] : Fin 2 → ℝ) ∈ GoodSet Y B E} y := by
  have hlast : (![M, y] : Fin 2 → ℝ) (Fin.last 1) = y := rfl
  have hsnoc : ∀ t : ℝ, Fin.snoc (Fin.init (![M, y] : Fin 2 → ℝ)) t = ![M, t] := by
    intro t; ext i; fin_cases i <;> rfl
  have hset : {t : ℝ | Fin.snoc (Fin.init (![M, y] : Fin 2 → ℝ)) t ∈ GoodSet Y B E} =
      {t : ℝ | (![M, t] : Fin 2 → ℝ) ∈ GoodSet Y B E} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    rw [hsnoc t]
  unfold GoodGraph
  simp only [Set.mem_ofPred_eq]
  rw [hlast, hset]

lemma goodSet_definable (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ))
    (E : Set ℝ)
    (hdef : (∅ : Set ℝ).Definable LRc
      {v : Fin 2 → ℝ | v 0 ∈ BadScale Y B E (v 1)}) :
    (∅ : Set ℝ).Definable LRc (GoodSet Y B E) := by
  have hdu : (Set.univ : Set ℝ).Definable LRc
      {v : Fin 2 → ℝ | v 0 ∈ BadScale Y B E (v 1)} := hdef.mono (Set.empty_subset _)
  have h0 : (Set.univ : Set ℝ).Definable LRc {v : Fin 2 → ℝ | 0 ≤ v 1} := by
    have h := definable_le_LRc (σ := Fin 2) (MvPolynomial.C (0 : ℝ)) (MvPolynomial.X (1 : Fin 2))
    convert h using 1
    ext v
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have h1 : (Set.univ : Set ℝ).Definable LRc {v : Fin 2 → ℝ | v 1 ≤ 1} := by
    have h := definable_le_LRc (σ := Fin 2) (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C (1 : ℝ))
    convert h using 1
    ext v
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have hU : (Set.univ : Set ℝ).Definable LRc (GoodSet Y B E) := by
    have h := (hdu.compl.inter h0).inter h1
    convert h using 1
    ext v
    simp only [GoodSet, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
  exact (definable_univ_iff_empty).mp hU

lemma goodGraph_definable (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ))
    (E : Set ℝ)
    (hdef : (∅ : Set ℝ).Definable LRc
      {v : Fin 2 → ℝ | v 0 ∈ BadScale Y B E (v 1)}) :
    (∅ : Set ℝ).Definable LRc (GoodGraph Y B E) :=
  definable_isGLB_family (goodSet_definable Y B E hdef)

/-- `GoodGraph` is functional in the scale: an `IsGLB` is unique. -/
lemma goodGraph_functional (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ))
    (E : Set ℝ) :
    ∀ M a b : ℝ, (![M, a] : Fin 2 → ℝ) ∈ GoodGraph Y B E →
      (![M, b] : Fin 2 → ℝ) ∈ GoodGraph Y B E → a = b := by
  intro M a b ha hb
  rw [mem_goodGraph_iff] at ha hb
  exact ha.unique hb

/-- `GoodGraph` tends to `0`: the hypothesis `hdec` provides, for every `ε > 0`, a tolerance
`δ = min (ε/2) (1/2) ∈ (0,1]` that is good at every large scale, and so bounds the least good
tolerance from above at those scales. -/
lemma goodGraph_tendsto_zero (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ))
    (E : Set ℝ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ M : ℝ, R ≤ M → M ∉ BadScale Y B E ε) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ M y : ℝ, R ≤ M →
      (![M, y] : Fin 2 → ℝ) ∈ GoodGraph Y B E → y < ε := by
  intro ε hε
  obtain ⟨R, hR⟩ := hdec (min (ε / 2) (1 / 2)) (lt_min (by linarith) (by norm_num))
  refine ⟨R, fun M y hM hy => ?_⟩
  rw [mem_goodGraph_iff] at hy
  have hmem : min (ε / 2) (1 / 2) ∈ {t : ℝ | (![M, t] : Fin 2 → ℝ) ∈ GoodSet Y B E} := by
    rw [Set.mem_ofPred_eq, mem_goodSet]
    refine ⟨hR M hM, le_of_lt (lt_min (by linarith) (by norm_num)), ?_⟩
    have := min_le_right (ε / 2) (1 / 2)
    linarith
  have hyδ := hy.1 hmem
  have : min (ε / 2) (1 / 2) < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  linarith

end BadScaleRate

/-
  Upgrade the qualitative decay of `BadScale` to the quantitative rate needed by the telescoping.
  Here `hbiff` is the pointwise equivalence `M ∈ BadScale Y B E ε ↔ 0 < M ∧ ¬ DevBdd Y B E M ε`.

  Route.  `BadScale Y B E ε` is downward closed in the scale: if `x` is `M`-deep (`IsDeepR B c M x`)
  then it is `M'`-deep for every `0 < M' ≤ M` (the window `[x/(2M'), 2M'x]` is smaller), hence a
  bad scale stays bad at every smaller positive scale.  So the "good" set
  `G ε = {M | 0 < M ∧ M ∉ BadScale Y B E ε}` is upward closed, and by `hdec` it is nonempty for
  every `ε > 0`.  Then `M > inf (G ε)` forces `M ∈ G ε`, and `hbiff` turns that into
  `DevBdd Y B E M ε`.  Consequently it suffices to produce *any* polynomial bound
  `inf (G ε) ≤ β · ε^{-n}` (large `ε`) for the threshold.

  Concretely: the truncated deviation function
      `δ M := sup {min ε 1 | M ∈ BadScale Y B E ε}`
  (`= min (sup {ε | M ∈ BadScale Y B E ε}) 1`) is bounded by `1`, non-increasing in `M`, and
  tends to `0` at `+∞` by `hdec`.  Its graph is `∅`-definable: it is the graph of the supremum of
  the vertical fibres of the definable family `{(M, ε) | M ∈ BadScale Y B E ε}` (given by `hdef`),
  which is `Submission.Work.WilC4.definable_isGLB_family` applied after negating the first
  coordinate (a `Fin 1`-quantifier bookkeeping, as in that file).  Then
  `Submission.Work.WilC4.pb_decay` (in the `Route.pb_decay` spelling, whose hypothesis is exactly
  `δ M < ε` eventually) gives `δ M ≤ β M^{-η}` with `η : ℚ`, `η > 0`, `β > 0`; and for `M` with
  `β M^{-η} < 1` this forces `sup {ε | M ∈ BadScale Y B E ε} = δ M ≤ β M^{-η}`, i.e.
  `M ∉ BadScale Y B E (β M^{-η})`, i.e. `DevBdd Y B E M (β M^{-η})` by `hbiff`.

  The file must not import `Submission.Work.WilC4.DevBddDefs` nor `dev_rate`, `dev_rate_devBdd`,
  `DevBdd_definable`, `DevDeep_definable`, `DevRatW_definable`, `DevConc_definable`: the index
  abbreviations `dc dx dw dy` there collide with those of
  `Submission.Work.WilC4.DeepThetaGDefs`, which sits in the import closure of `deep_ratio_bdd` /
  `dev_decay_E`.  `ULPMDev`, `pb_decay`, `pb_poly_bound`, `definable_isGLB_family` are fine.
-/
theorem badScale_rate {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (B : Set (Fin (k + 1) → ℝ)) (hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B)
    (E : Set ℝ) (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E)
    (hbiff : ∀ (M ε : ℝ), M ∈ Work.WilC4.BadScale Y B E ε ↔
      0 < M ∧ ¬ Work.WilC4.DevBdd Y B E M ε)
    (hdef : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : Fin 2 → ℝ | v 0 ∈ Work.WilC4.BadScale Y B E (v 1)})
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ M : ℝ, R ≤ M →
      M ∉ Work.WilC4.BadScale Y B E ε) :
    ∃ (η : ℚ) (β : ℝ), 0 < η ∧ 0 < β ∧ ∃ R : ℝ, ∀ M : ℝ, R ≤ M →
      Work.WilC4.DevBdd Y B E M (β * M ^ (-(η : ℝ))) := by
  -- The least good tolerance is polynomially bounded: `pb_decay` applied to `GoodGraph`.
  obtain ⟨η, β, hη, hβ, R₀, hR₀⟩ :=
    pb_decay hR hPB (goodGraph_definable Y B E hdef)
      (fun M a b ha hb => goodGraph_functional Y B E M a b ha hb)
      (goodGraph_tendsto_zero Y B E hdec)
  -- `hdec` at tolerance `1` gives a scale beyond which tolerance `1` is good.
  obtain ⟨R₁, hR₁⟩ := hdec 1 one_pos
  refine ⟨η, 2 * β, hη, by positivity, max (max R₀ R₁) 1, fun M hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := le_trans (le_max_right (max R₀ R₁) 1) hM
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMR₀ : R₀ ≤ M := le_trans (le_trans (le_max_left R₀ R₁) (le_max_left (max R₀ R₁) 1)) hM
  have hMR₁ : R₁ ≤ M := le_trans (le_trans (le_max_right R₀ R₁) (le_max_left (max R₀ R₁) 1)) hM
  have hnotbad1 : M ∉ BadScale Y B E 1 := hR₁ M hMR₁
  -- the fibre of good tolerances `S = {ε ∈ [0,1] | M ∉ BadScale ε}` is nonempty and bounded below
  set S : Set ℝ := {t : ℝ | (![M, t] : Fin 2 → ℝ) ∈ GoodSet Y B E} with hS
  have hSmem : ∀ t : ℝ, t ∈ S ↔ M ∉ BadScale Y B E t ∧ 0 ≤ t ∧ t ≤ 1 := by
    intro t
    rw [hS]
    simp only [Set.mem_ofPred_eq]
    rw [mem_goodSet]
  have hne : S.Nonempty := ⟨1, (hSmem 1).mpr ⟨hnotbad1, by norm_num, le_rfl⟩⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ((hSmem t).mp ht).2.1⟩
  have hglb : IsGLB S (sInf S) := Real.isGLB_sInf hne hbdd
  have hgG : (![M, sInf S] : Fin 2 → ℝ) ∈ GoodGraph Y B E :=
    (mem_goodGraph_iff Y B E M (sInf S)).mpr hglb
  have hgb : sInf S ≤ β * M ^ (-(η : ℝ)) := hR₀ M (sInf S) hMR₀ hgG
  -- `sInf S ≥ 0`, and the good tolerance `β M^{-η}` is *strictly* larger than the least one
  have hg0 : 0 ≤ sInf S := hglb.2 (fun t ht => ((hSmem t).mp ht).2.1)
  have hrpow : 0 < M ^ (-(η : ℝ)) := Real.rpow_pos_of_pos hM0 _
  have hbpos : 0 < β * M ^ (-(η : ℝ)) := mul_pos hβ hrpow
  have hlt : sInf S < (2 * β) * M ^ (-(η : ℝ)) := by
    have h2 : (2 * β) * M ^ (-(η : ℝ)) = 2 * (β * M ^ (-(η : ℝ))) := by ring
    rw [h2]; nlinarith [hgb, hbpos]
  -- strictness: `(2β) M^{-η}` is not a lower bound of `S`, so some good tolerance lies below it
  have hntlb : ¬ (∀ t ∈ S, (2 * β) * M ^ (-(η : ℝ)) ≤ t) := by
    intro h
    have := hglb.2 h
    linarith
  push Not at hntlb
  obtain ⟨t, htm, htt⟩ := hntlb
  have htnb : M ∉ BadScale Y B E t := ((hSmem t).mp htm).1
  have hynb : M ∉ BadScale Y B E ((2 * β) * M ^ (-(η : ℝ))) :=
    not_mem_badScale_mono Y B E (le_of_lt htt) htnb
  by_contra hcon
  exact hynb ((hbiff M ((2 * β) * M ^ (-(η : ℝ)))).mpr ⟨hM0, hcon⟩)

end Work.WilC4
