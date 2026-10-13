/-
  WilC4/realULPM : H1 of the C4 route, `Route.ModelULPM ℝ` from `hR`, `hOM`, `hPB`.

  ## Assembly of the ULPM proof (steps 0-10 of `ULPM_E_DEV.md` / `wilkies_C4_route.md` §4)

  Inputs used (all proved elsewhere in `Submission/Work/WilC4/`, imported below):

  * `ulpm_crit` — off a ∅-definable `Bc` with uniformly bounded fibres: the domain and the zero set
    of the fibre of `Y` are all-or-nothing on every interval;
  * `ulpm_mono_param` — off a ∅-definable family with uniformly bounded fibres: the fibre of
    `UlpmTot Y`, and its doubling ratio, satisfy the three-point monotonicity trichotomy;
  * `exists_ulpmB` + `ulpmStruct_of_ulpmB_tot` — package the above into `ULPMStruct (UlpmTot Y) B₀`
    with `B₀ ⊇ Bm` (the ratio-monotonicity family);
  * `ulpm_E_finite`, `clusterE_subset_rpow_rat`, `ClusterER_definable_self` — the exponent set
    `E := Route.ClusterE (UlpmTot Y) B₀` is finite, ∅-definable and contained in `{0} ∪ 2^ℚ`;
  * `ulpm_Bx` — the crossing-augmented breakpoint family `B ⊇ B₀ ∪ Bc ∪ BfT ∪ Bm` with uniformly
    bounded fibres, off which the doubling ratio is confined to a single band of `Mid E`;
  * `deep_ratio_scale_bdd` — the doubling ratios at **`Γ`-deep** points are `< Γ` (a *constant*
    scale `Γ`), the "PB-diagonal" bound (P2 of `wilkies_C4_route.md` §4);
  * `dev_decay_E_deep` (file `DevDecayEDeep.lean`) — the deviation of the deep ratios from `E`
    decays like a negative rational power of the scale.  This is the version of `dev_decay_E` whose
    only ratio input is the **`Γ`-deep** bound above; it is *not* `dev_decay_E`, which asks for a
    bound at scale `2` and whose route through `caseA_bad_bounded_zero`/`cbz_flat` therefore needs
    the (FALSE, see `wilkies_c5c4_ruling.md`) statement `short_window_ratio_bdd`.
  * `slot_bound` — the telescoping inside one slot, producing `q ∈ ExpSet E` and the two `IsRpow`
    inequalities;
  * `sameSide_slot` — a `SameSide` pair sits in a genuine slot;
  * `mono_valY_of_trichotomy`, `ClusterE_mono`, `ULPMStruct_mono`, `expSet_toFinset`,
    `ulpmTot_eq_of_ne_zero` — glue.

  ## Why the ratio input is taken at the *constant* scale `Γ` (repair of 2026-10-11)

  `hbdd` at scale `2` is *not* available: the short-window statement
  `Work.WilC4.short_window_ratio_bdd` (equivalently `ratW_le_of_no_deep_pair`,
  `deep_ratio_tight`, `deep_ratio_bdd`) is **false** (three linear ramps of increasing height at
  `z, 2z, 4z`; see `wilkies_c5c4_ruling.md`).  It is *not needed*: the ratio bound is consumed only
  in `cbz_flat` (through `caseA_bad_bounded_zero`), on the region `[N/M, M/N]` of the witness, and
  every point `x·t`, `t ∈ [N/M, M/N]`, of that region is `N`-deep (take `N ≥ Γ`) — so the
  *constant* `Γ`-deep bound `|w| < Γ` applies there with `Cbdd := Γ`.  The repaired chain is
  `deep_ratio_scale_bdd → cbz_flat_deep → caseA_bad_bounded_zero_deep → dev_decay_E_deep`,
  which is what this file uses.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.ULPMRoute
import Submission.Work.WilC4.ULPMExp
import Submission.Work.WilC4.ULPMAsm
import Submission.Work.WilC4.ULPMB
import Submission.Work.WilC4.ulpm_mono_param
import Submission.Work.WilC4.ulpm_crit
import Submission.Work.WilC4.ulpm_E_finite
import Submission.Work.WilC4.ulpmTot_definable
import Submission.Work.WilC4.ratGraph_definable
import Submission.Work.WilC4.ulpm_Bx
import Submission.Work.WilC4.clusterE_subset_rpow_rat
import Submission.Work.WilC4.ClusterER_definable_self
import Submission.Work.WilC4.deep_ratio_scale_bdd
import Submission.Work.WilC4.dev_decay_E
import Submission.Work.WilC4.DevDecayEDeep
import Submission.Work.WilC4.slot_bound
import Submission.Work.WilC4.sameSide_slot
import Submission.Work.WilC4.badScale_definable
import Submission.Work.WilC4.badScale_rate

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG Work.WilC4.Route

/-- `IsRpow x 0 1` for every `x` (`1 = x ^ 0`). -/
private theorem isRpow_zero_one (x : ℝ) : Work.WilC4.IsRpow x 0 1 :=
  ⟨0, 1, one_pos, by norm_num, by norm_num, Or.inr ⟨1, one_ne_zero, by norm_num⟩⟩

/-- Cardinality bound for a union of four sets of reals. -/
private theorem encard_union4 (A Bb C D : Set ℝ) (a b c d : ℕ) (ha : A.encard ≤ a)
    (hb : Bb.encard ≤ b) (hc : C.encard ≤ c) (hd : D.encard ≤ d) :
    (A ∪ Bb ∪ C ∪ D).encard ≤ ((a + b + c + d : ℕ) : ENat) := by
  have h1 : (A ∪ Bb).encard ≤ ((a + b : ℕ) : ENat) := by
    refine le_trans (Set.encard_union_le A Bb) ?_
    rw [Nat.cast_add]; exact add_le_add ha hb
  have h2 : (A ∪ Bb ∪ C).encard ≤ ((a + b + c : ℕ) : ENat) := by
    refine le_trans (Set.encard_union_le (A ∪ Bb) C) ?_
    rw [Nat.cast_add]; exact add_le_add h1 hc
  have h3 : (A ∪ Bb ∪ C ∪ D).encard ≤ ((a + b + c + d : ℕ) : ENat) := by
    refine le_trans (Set.encard_union_le (A ∪ Bb ∪ C) D) ?_
    rw [Nat.cast_add]; exact add_le_add h2 hd
  exact h3

theorem realULPM (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ) (hOM : WilkiesDesign.CG.OMinModels) (hPB : WilkiesDesign.CG.PolyBoundedRExp) : Work.WilC4.Route.ModelULPM ℝ := by
  intro k Y hY hfun
  -- ## 0. Totalise and de-zero the family
  have hYT : (∅ : Set ℝ).Definable LRc (UlpmTot Y) := ulpmTot_definable hY
  have hfunT : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr (UlpmTot Y) c x y →
      Gr (UlpmTot Y) c x y' → y = y' := ulpmTot_functional hfun
  -- ## 1. The three breakpoint families
  --  * `Bc`: domain/zero dichotomy of `Y` (for the domain and zero clauses of `ModelULPM`)
  obtain ⟨Nc, Bc, hBcdef, hBccard, hcrit⟩ := ulpm_crit (k := k) hOM Y hY hfun
  --  * `BfT`: monotonicity of the fibre of the totalised family
  obtain ⟨NfT, BfT, hBfTdef, hBfTcard, htriT⟩ := ulpm_mono_param (k := k) hOM (UlpmTot Y) hYT hfunT
  --  * `Bm`: monotonicity of the doubling ratio of the totalised family
  obtain ⟨Nm, Bm, hBmdef, hBmcard, htriM⟩ :=
    ulpm_mono_param (k := k) hOM (RatGraph (UlpmTot Y)) (ratGraph_definable hYT)
      (ratGraph_is_graph hfunT)
  -- the ratio-monotonicity trichotomy in the `RatW` spelling
  have htriM' : ∀ (c : Fin k → ℝ) (a b : ℝ), a < b →
      (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ Bm) →
      ∀ x₁ x₂ x₃ w₁ w₂ w₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b →
        x₃ ∈ Set.Ioo a b → x₁ < x₂ → x₂ < x₃ → RatW (UlpmTot Y) c x₁ w₁ →
        RatW (UlpmTot Y) c x₂ w₂ → RatW (UlpmTot Y) c x₃ w₃ →
        (w₁ ≤ w₂ ∧ w₂ ≤ w₃) ∨ (w₃ ≤ w₂ ∧ w₂ ≤ w₁) :=
    fun c a b hab hfree x₁ x₂ x₃ w₁ w₂ w₃ hx₁ hx₂ hx₃ h12 h23 hw₁ hw₂ hw₃ =>
      htriM c a b hab hfree x₁ x₂ x₃ w₁ w₂ w₃ hx₁ hx₂ hx₃ h12 h23
        ((ratGraph_mem_iff (UlpmTot Y) c x₁ w₁).mpr hw₁)
        ((ratGraph_mem_iff (UlpmTot Y) c x₂ w₂).mpr hw₂)
        ((ratGraph_mem_iff (UlpmTot Y) c x₃ w₃).mpr hw₃)
  -- ## 2. `ULPMStruct (UlpmTot Y) B₀`
  obtain ⟨N₀, B₀, hB₀def, hB₀card, hULPMB⟩ :=
    exists_ulpmB (k := k) hOM (UlpmTot Y) hYT hfunT Bm hBmdef Nm hBmcard htriM'
  have hst₀ : ULPMStruct (UlpmTot Y) B₀ := ulpmStruct_of_ulpmB_tot hfun hULPMB
  -- ## 3. The exponent set `E`
  let E : Set ℝ := Route.ClusterE (UlpmTot Y) B₀
  have hEfin : E.Finite := ulpm_E_finite hR hOM hPB (UlpmTot Y) hYT hfunT B₀ hB₀def hst₀.1
  have hEdef : (∅ : Set ℝ).Definable₁ LRc E := by
    have h := ClusterER_definable_self (UlpmTot Y) B₀ hYT hB₀def
    rwa [← ClusterE_eq_ClusterER] at h
  have hEsq : E ⊆ ({0} : Set ℝ) ∪ Set.range (fun q : ℚ => (2 : ℝ) ^ (q : ℝ)) :=
    clusterE_subset_rpow_rat hR hOM hPB (UlpmTot Y) hYT hfunT B₀ hB₀def hst₀.1
  -- ## 4. The final crossing-augmented breakpoint family `B`
  let B₀' : Set (Fin (k + 1) → ℝ) := ((B₀ ∪ Bc) ∪ BfT) ∪ Bm
  have hB₀'def : (∅ : Set ℝ).Definable LRc B₀' := by
    dsimp only [B₀']; exact ((hB₀def.union hBcdef).union hBfTdef).union hBmdef
  have hB₀'card : ∀ c : Fin k → ℝ,
      {x : ℝ | Fin.cons x c ∈ B₀'}.encard ≤ N₀ + Nc + NfT + Nm := by
    intro c
    have hfib : {x : ℝ | Fin.cons x c ∈ B₀'} =
        ({x : ℝ | Fin.cons x c ∈ B₀} ∪ {x : ℝ | Fin.cons x c ∈ Bc} ∪
          {x : ℝ | Fin.cons x c ∈ BfT} ∪ {x : ℝ | Fin.cons x c ∈ Bm}) := by
      ext x; simp only [B₀', Set.mem_setOf_eq, Set.mem_union]
    rw [hfib]
    exact encard_union4 _ _ _ _ _ _ _ _ (hB₀card c) (hBccard c) (hBfTcard c) (hBmcard c)
  -- the four families are all contained in `B₀'`
  have hB₀in : B₀ ⊆ B₀' := by intro x hx; simp only [B₀', Set.mem_union]; tauto
  have hBcin : Bc ⊆ B₀' := by intro x hx; simp only [B₀', Set.mem_union]; tauto
  have hBfTin : BfT ⊆ B₀' := by intro x hx; simp only [B₀', Set.mem_union]; tauto
  have hmin : Bm ⊆ B₀' := by intro x hx; simp only [B₀', Set.mem_union]; tauto
  have hmono₀' : ∀ (c : Fin k → ℝ) (a b : ℝ), a < b →
      (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀') →
      ∀ x₁ x₂ x₃ w₁ w₂ w₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b →
        x₃ ∈ Set.Ioo a b → x₁ < x₂ → x₂ < x₃ → RatW (UlpmTot Y) c x₁ w₁ →
        RatW (UlpmTot Y) c x₂ w₂ → RatW (UlpmTot Y) c x₃ w₃ →
        (w₁ ≤ w₂ ∧ w₂ ≤ w₃) ∨ (w₃ ≤ w₂ ∧ w₂ ≤ w₁) :=
    fun c a b hab hfree x₁ x₂ x₃ w₁ w₂ w₃ hx₁ hx₂ hx₃ h12 h23 hw₁ hw₂ hw₃ =>
      hULPMB.2 c a b hab (fun x hx hxB₀ => hfree x hx (hB₀in hxB₀))
        x₁ x₂ x₃ w₁ w₂ w₃ hx₁ hx₂ hx₃ h12 h23 hw₁ hw₂ hw₃
  obtain ⟨N₁, B, hBdef, hBcard, hsub', hband⟩ :=
    ulpm_Bx (k := k) hOM (UlpmTot Y) hYT B₀' hB₀'def (N₀ + Nc + NfT + Nm) hB₀'card hmono₀'
      E hEdef hEfin
  have hB₀sub : B₀ ⊆ B := fun x hx => hsub' (hB₀in hx)
  have hBcsub : Bc ⊆ B := fun x hx => hsub' (hBcin hx)
  have hBfTsub : BfT ⊆ B := fun x hx => hsub' (hBfTin hx)
  have hsubE : Route.ClusterE (UlpmTot Y) B ⊆ E := ClusterE_mono hB₀sub
  -- ## 5. The uniform bound on the deep (Γ-deep) doubling ratios (`deep_ratio_scale_bdd`)
  obtain ⟨Γd, hΓd, hscale⟩ :=
    deep_ratio_scale_bdd hR hOM hPB (UlpmTot Y) hYT hfunT B₀ hB₀def hst₀
  have hdd : ∃ Γ : ℝ, 2 ≤ Γ ∧ ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x →
      IsDeepR B c Γ x → RatW (UlpmTot Y) c x w → |w| < Γ :=
    ⟨max Γd 2, le_max_right _ _,
      fun c x w hx hdeep hrat =>
        hscale (max Γd 2) (le_max_left _ _) c x w hx (IsDeepR.mono_B hB₀sub hdeep) hrat⟩
  -- ## 6. The deviation rate
  have hdec := dev_decay_E_deep hR hOM hPB (UlpmTot Y) hYT hfunT B₀ hB₀def hst₀ E hEfin N₁
    B hBdef hB₀sub hsubE hBcard hband hdd
  -- the pointwise equivalence between `BadScale` and the negation of `DevBdd`
  have hbiff : ∀ M ε : ℝ, M ∈ BadScale (UlpmTot Y) B E ε ↔
      0 < M ∧ ¬ DevBdd (UlpmTot Y) B E M ε := by
    intro M ε
    constructor
    · rintro ⟨hM, c, x, w, hx, hdeep, hrat, hbad⟩
      refine ⟨hM, fun hbdd => ?_⟩
      obtain ⟨ρ, hρE, hρpos, hle⟩ := hbdd c x w hx hdeep hrat
      exact absurd hle (not_le.mpr (hbad ρ hρE hρpos))
    · rintro ⟨hM, hnot⟩
      simp only [DevBdd] at hnot
      push_neg at hnot
      obtain ⟨c, x, w, hx, hdeep, hrat, hbad⟩ := hnot
      exact ⟨hM, c, x, w, hx, hdeep, hrat, fun ρ hρE hρpos => hbad ρ hρE hρpos⟩
  have hdefBS : (∅ : Set ℝ).Definable LRc
      {v : Fin 2 → ℝ | v 0 ∈ BadScale (UlpmTot Y) B E (v 1)} :=
    badScale_definable (UlpmTot Y) hYT B hBdef E hEdef
  obtain ⟨η, β, hη, hβ, Rdev, hrate⟩ :=
    badScale_rate hR hPB (UlpmTot Y) hYT hfunT B hBdef E hEdef hbiff hdefBS hdec
  have hdev' : ∀ M : ℝ, Rdev ≤ M → ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x →
      IsDeepR B c M x → RatW (UlpmTot Y) c x w →
      ∃ ρ ∈ E, 0 < ρ ∧ |w / ρ - 1| ≤ β * M ^ (-(η : ℝ)) :=
    fun M hM => hrate M hM
  have hdev : ∃ R : ℝ, ∀ M : ℝ, R ≤ M → ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x →
      IsDeepR B c M x → RatW (UlpmTot Y) c x w →
      ∃ ρ ∈ E, 0 < ρ ∧ |w / ρ - 1| ≤ β * M ^ (-(η : ℝ)) :=
    ⟨Rdev, hdev'⟩
  -- ## 6b. A positive element of `E`, from the deviation bound at an explicit deep point
  have hEne : ∃ ρ ∈ E, 0 < ρ := by
    let c₀ : Fin k → ℝ := 0
    have hfin₀ : ({b : ℝ | Fin.cons b c₀ ∈ B}).Finite :=
      Set.encard_lt_top_iff.mp (lt_of_le_of_lt (hBcard c₀) (WithTop.coe_lt_top N₁))
    obtain ⟨q, hq⟩ := hfin₀.bddAbove
    let M : ℝ := max Rdev 1
    have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
    have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
    have hMR : Rdev ≤ M := le_max_left _ _
    let x : ℝ := 2 * M * (|q| + 1)
    have hxpos : 0 < x := by dsimp only [x]; nlinarith [hMpos, abs_nonneg q]
    have hx2M : x / (2 * M) = |q| + 1 := by
      dsimp only [x]; exact mul_div_cancel_left₀ (|q| + 1) (by positivity)
    have hdeep : IsDeepR B c₀ M x := by
      intro b hb
      rintro ⟨hle, -⟩
      rw [hx2M] at hle
      have hbq : b ≤ q := hq hb
      linarith [hbq, le_abs_self q, hle]
    have hrat : RatW (UlpmTot Y) c₀ x (ratioY (UlpmTot Y) c₀ x) := by
      refine (ratW_iff_valY hfunT c₀ x _).mpr ⟨?_, ?_, ?_, rfl⟩
      · obtain ⟨y, hy⟩ := ulpmTot_total Y c₀ x
        exact valY_mem (UlpmTot Y) c₀ x ⟨y, hy⟩
      · obtain ⟨y, hy⟩ := ulpmTot_total Y c₀ (2 * x)
        exact valY_mem (UlpmTot Y) c₀ (2 * x) ⟨y, hy⟩
      · obtain ⟨y, hy⟩ := ulpmTot_total Y c₀ x
        exact ulpmTot_ne Y c₀ x (valY (UlpmTot Y) c₀ x) (valY_mem (UlpmTot Y) c₀ x ⟨y, hy⟩)
    obtain ⟨ρ, hρE, hρpos, -⟩ := hdev' M hMR c₀ x (ratioY (UlpmTot Y) c₀ x) hxpos hdeep hrat
    exact ⟨ρ, hρE, hρpos⟩
  -- ## 7. Monotonicity of the fibre of `UlpmTot Y` off `B`
  have hgf : GoodFibre (UlpmTot Y) B := (ULPMStruct_mono hB₀sub hst₀).1
  have hfmono : ∀ (c : Fin k → ℝ) (a b : ℝ), a < b →
      (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) →
      MonotoneOn (valY (UlpmTot Y) c) (Set.Ioo a b) ∨
        AntitoneOn (valY (UlpmTot Y) c) (Set.Ioo a b) :=
    fun c a b hab hfree =>
      mono_valY_of_trichotomy hfunT hgf hab hfree
        (fun x₁ x₂ x₃ y₁ y₂ y₃ hx₁ hx₂ hx₃ h12 h23 hy₁ hy₂ hy₃ =>
          htriT c a b hab (fun x hx hxB => hfree x hx (hBfTsub hxB))
            x₁ x₂ x₃ y₁ y₂ y₃ hx₁ hx₂ hx₃ h12 h23 hy₁ hy₂ hy₃)
  -- ## 8. The telescoping inside a slot
  obtain ⟨N₂, hN₂, hslot⟩ := slot_bound hη hβ hfunT hB₀sub hst₀ hfmono hdev hEfin hEne hEsq
  -- ## 9. The final uniform data
  let NN : ℕ := max N₁ (max N₂ 2)
  have hNNpos : 0 < NN :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_max_right N₂ 2) (le_max_right N₁ (max N₂ 2)))
  have hNNge2 : 2 ≤ NN := le_trans (le_max_right N₂ 2) (le_max_right N₁ (max N₂ 2))
  have hN₂le : N₂ ≤ NN := le_trans (le_max_left N₂ 2) (le_max_right N₁ (max N₂ 2))
  have hN₁le : N₁ ≤ NN := le_max_left N₁ (max N₂ 2)
  refine ⟨NN, hNNpos, (expSet_finite hEfin).toFinset, B, hBdef, fun c => ⟨?_, ?_⟩⟩
  · exact le_trans (hBcard c) (by exact_mod_cast hN₁le)
  · -- the model-theoretic conclusion, for a fixed parameter tuple `c`
    intro x₁ x₂ hx₁ hx₂ hss
    have hNge1 : (1 : ℝ) ≤ (NN : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) hNNge2)
    have hBfin : ({x : ℝ | Fin.cons x c ∈ B}).Finite :=
      Set.encard_lt_top_iff.mp (lt_of_le_of_lt (hBcard c) (WithTop.coe_lt_top N₁))
    -- the case `x₁ ≤ x₂`; the other case follows by symmetry of everything involved
    have key : ∀ x₁ x₂ : ℝ, 0 < x₁ → 0 < x₂ → x₁ ≤ x₂ →
        SameSide NN {x : ℝ | Fin.cons x c ∈ B} x₁ x₂ →
        ((∃ y, Gr Y c x₁ y) ↔ (∃ y, Gr Y c x₂ y)) ∧
        ∀ y₁ y₂ : ℝ, Gr Y c x₁ y₁ → Gr Y c x₂ y₂ →
          ∃ q ∈ (expSet_finite hEfin).toFinset, ∃ t₁ t₂ : ℝ,
            IsRpow x₁ q t₁ ∧ IsRpow x₂ q t₂ ∧
            |y₂| * t₁ ≤ (NN : ℝ) * (|y₁| * t₂) ∧
            |y₁| * t₂ ≤ (NN : ℝ) * (|y₂| * t₁) := by
      intro x₁ x₂ hx₁ hx₂ hle hss
      obtain ⟨a, b, ha, hab, hfree, hNa, hNb⟩ :=
        sameSide_slot NN hNNge2 hBfin hx₁ hle hss
      have hx₁mem : x₁ ∈ Set.Ioo a b :=
        ⟨by nlinarith [mul_le_mul_of_nonneg_right hNge1 ha.le, hNa],
         by nlinarith [hNb, hle, mul_le_mul_of_nonneg_right hNge1 hx₂.le]⟩
      have hx₂mem : x₂ ∈ Set.Ioo a b :=
        ⟨by nlinarith [hNa, hle, ha], by nlinarith [hNb, mul_le_mul_of_nonneg_right hNge1 hx₂.le]⟩
      have hfreeBc : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ Bc :=
        fun x hx hxB => hfree x hx (hBcsub hxB)
      obtain ⟨hDom, hZero, -⟩ := hcrit c a b hab hfreeBc
      constructor
      · constructor
        · intro ⟨y, hy⟩
          exact hDom ⟨x₁, hx₁mem, y, hy⟩ x₂ hx₂mem
        · intro ⟨y, hy⟩
          exact hDom ⟨x₂, hx₂mem, y, hy⟩ x₁ hx₁mem
      · intro y₁ y₂ hy₁ hy₂
        by_cases hz : ∃ x ∈ Set.Ioo a b, Gr Y c x 0
        · -- the fibre vanishes identically on the slot: both values are `0`
          have hzero : ∀ x ∈ Set.Ioo a b, Gr Y c x 0 := hZero hz
          have hy₁0 : y₁ = 0 := hfun c x₁ y₁ 0 hy₁ (hzero x₁ hx₁mem)
          have hy₂0 : y₂ = 0 := hfun c x₂ y₂ 0 hy₂ (hzero x₂ hx₂mem)
          refine ⟨0, ?_, 1, 1, isRpow_zero_one x₁, isRpow_zero_one x₂, ?_, ?_⟩
          · rw [← Finset.mem_coe, expSet_toFinset hEfin]
            exact mem_expSet.mpr (Or.inl rfl)
          · rw [hy₁0, hy₂0]; norm_num
          · rw [hy₁0, hy₂0]; norm_num
        · -- the fibre is nowhere zero on the slot: transfer to `UlpmTot Y`
          have hne : ∀ x ∈ Set.Ioo a b, ∀ y : ℝ, Gr Y c x y → y ≠ 0 := by
            intro x hx y hy hy0
            exact hz ⟨x, hx, hy0 ▸ hy⟩
          have hg₁ : Gr (UlpmTot Y) c x₁ y₁ :=
            ulpmTot_eq_of_ne_zero hy₁ (hne x₁ hx₁mem y₁ hy₁)
          have hg₂ : Gr (UlpmTot Y) c x₂ y₂ :=
            ulpmTot_eq_of_ne_zero hy₂ (hne x₂ hx₂mem y₂ hy₂)
          obtain ⟨q, hq, t₁, t₂, hR₁, hR₂, hi₁, hi₂⟩ :=
            hslot NN hN₂le c a b x₁ x₂ y₁ y₂ ha hab hfree
              (hband c a b hab hfree) hx₁ hx₂ hle hNa hNb hg₁ hg₂
          exact ⟨q, by rw [← Finset.mem_coe, expSet_toFinset hEfin]; exact hq,
            t₁, t₂, hR₁, hR₂, hi₁, hi₂⟩
    by_cases hle : x₁ ≤ x₂
    · exact key x₁ x₂ hx₁ hx₂ hle hss
    · -- swap the two points
      have hx₂x₁ : x₂ ≤ x₁ := le_of_lt (not_le.mp hle)
      have hss' : SameSide NN {x : ℝ | Fin.cons x c ∈ B} x₂ x₁ :=
        fun b hb => (hss b hb).elim (fun h => Or.inl ⟨h.2, h.1⟩) (fun h => Or.inr ⟨h.2, h.1⟩)
      have h := key x₂ x₁ hx₂ hx₁ hx₂x₁ hss'
      refine ⟨h.1.symm, fun y₁ y₂ hy₁ hy₂ => ?_⟩
      obtain ⟨q, hq, t₁, t₂, hR₁, hR₂, hi₁, hi₂⟩ := h.2 y₂ y₁ hy₂ hy₁
      exact ⟨q, hq, t₂, t₁, hR₂, hR₁, hi₂, hi₁⟩

end Work.WilC4
