/-
  WilVP N1: **uniform iso-balls on `ℝ`** (file `N1_iso.lean`).

  `isoBall_real : Work.WilC4.Route.ModelULPM ℝ → OMinModels → IsoBallProp ℝ`.

  Route (design §1, review fixes F3/F6):
  * `P_c` is the union of the monotonicity breakpoints of the iso-radius `ρ_c` (from
    `Work.WilC4.ulpm_mono_param` applied to `Work.WilVP.RhoFam`) with the boundary points of the
    domain fibre (`DomFam`) and of the zero fibre (`ZeroFam`) of `Y` (from
    `Work.WilVP.boundary_family`);
  * on a monotone piece `(p₁,p₂)` (bracketed by adjacent points of `P_c`), ULPM applied to the
    recentred family at the centre `p₁` plus the geometric-scale pigeonhole produce a
    breakpoint-free window, and `Work.WilVP.window_iso` turns it into a good radius (likewise for
    an antitone piece with the centre `p₂`);
  * monotonicity of `ρ` carries the bound to `x`, and `0 < N·|y−x| < dist(x,P_c)` lets `y` into a
    good ball around `x`.
-/
import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilVP.scale_pigeonhole
import Submission.Work.WilVP.window_iso
import Submission.Work.WilVP.window_rho_lower
import Submission.Work.WilVP.piece_lower_mono
import Submission.Work.WilVP.piece_lower_anti
import Submission.Work.WilVP.rhoFam_definable
import Submission.Work.WilVP.rho_exists_unique
import Submission.Work.WilVP.isoGood_of_lt_rho
import Submission.Work.WilVP.le_rho_of_isoGood
import Submission.Work.WilVP.boundary_family
import Submission.Work.WilVP.domFam_definable
import Submission.Work.WilVP.zeroFam_definable
import Submission.Work.WilVP.piece_adjacent
import Submission.Work.WilVP.piece_subset_of_notBnd
import Submission.Work.WilVP.exists_bnd_below_above
import Submission.Work.WilVP.shift_ulpm_data
import Submission.Work.WilC4.ulpm_mono_param
import Submission.Work.WilC4.mono_of_three_point
import Submission.Work.WilC2.gap_subset_of_bnd

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open Classical
open WilkiesDesign WilkiesDesign.CG FirstOrder FirstOrder.Language

namespace Work.WilVP

/-! ## 0. Small helpers -/

/-- `IsoGood` is monotone in the factor `K`. -/
theorem IsoGood_mono_factor {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {K K' : ℝ} {c : Fin k → ℝ}
    {x y₀ r : ℝ} (h : IsoGood Y K c x y₀ r) (hKK' : K ≤ K') : IsoGood Y K' c x y₀ r := by
  intro u hu
  obtain ⟨y, hy, h1, h2⟩ := h u hu
  exact ⟨y, hy, le_trans h1 (mul_le_mul_of_nonneg_right hKK' (abs_nonneg y₀)),
    le_trans h2 (mul_le_mul_of_nonneg_right hKK' (abs_nonneg y))⟩

/-- `RhoFam Y K₀` is a family of graphs. -/
theorem rhoFam_fun {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {K₀ : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y') :
    ∀ (c' : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c') ∈ RhoFam Y K₀ →
      Fin.cons x (Fin.cons y' c') ∈ RhoFam Y K₀ → y = y' := by
  intro c' x y y' hy hy'
  rw [rhoFam_mem_iff] at hy hy'
  obtain ⟨z, hz, -, hglb⟩ := hy
  obtain ⟨z', hz', -, hglb'⟩ := hy'
  rw [hfun c' x z z' hz hz'] at hglb
  exact IsGLB.unique hglb hglb'

/-- `|(q:ℝ)|` is bounded by the ceiling of its absolute value. -/
theorem abs_rat_le_ceil_nat (q : ℚ) : |(q : ℝ)| ≤ ((⌈|(q : ℝ)|⌉₊ : ℕ) : ℝ) :=
  Nat.le_ceil _

/-- The union of three sets, for `encard` bookkeeping. -/
theorem encard_union3 {A Bb C : Set ℝ} {a b c : ℕ} (ha : A.encard ≤ a) (hb : Bb.encard ≤ b)
    (hc : C.encard ≤ c) : (A ∪ Bb ∪ C).encard ≤ ((a + b + c : ℕ) : ℕ∞) := by
  have h1 : (A ∪ Bb).encard ≤ ((a + b : ℕ) : ℕ∞) := by
    refine le_trans (Set.encard_union_le A Bb) ?_
    rw [Nat.cast_add]; exact add_le_add ha hb
  refine le_trans (Set.encard_union_le (A ∪ Bb) C) ?_
  rw [Nat.cast_add]; exact add_le_add h1 hc

/-- The set of `x` with `(x,c) ∈ P` is the union of three fibres. -/
theorem fibre_P_eq {k : ℕ} {B_mono PD PZ : Set (Fin (k + 1) → ℝ)} (c : Fin k → ℝ) :
    {x : ℝ | Fin.cons x c ∈ B_mono ∪ PD ∪ PZ} =
      ({x : ℝ | Fin.cons x c ∈ B_mono} ∪ {x : ℝ | Fin.cons x c ∈ PD}) ∪
        {x : ℝ | Fin.cons x c ∈ PZ} := by
  ext z; simp only [Set.mem_ofPred_eq, Set.mem_union]

/-! ## 1. The assembly -/

/-- **N1. Uniform iso-balls on `ℝ`**, from ULPM (C4's `realULPM`) and the proved parametric
monotonicity theorem `Work.WilC4.ulpm_mono_param`. -/
theorem isoBall_real (hU : Work.WilC4.Route.ModelULPM ℝ) (hOM : OMinModels) :
    IsoBallProp ℝ := by
  intro k Y hYdef hfun hbdd
  -- ## 1. ULPM data for the two recentrings
  obtain ⟨N₁, hN₁pos, Qs₁, B₁, hB₁def, hB₁card, hU₁⟩ := shift_ulpm_data hU hYdef hfun 1
  obtain ⟨N₂, hN₂pos, Qs₂, B₂, hB₂def, hB₂card, hU₂⟩ := shift_ulpm_data hU hYdef hfun (-1)
  -- ## 2. The constant `Qb` bounding all exponents
  let Qb : ℕ := (Qs₁ ∪ Qs₂).sup (fun q => ⌈|(q : ℝ)|⌉₊)
  have hQb₁ : ∀ q ∈ Qs₁, |(q : ℝ)| ≤ (Qb : ℝ) := by
    intro q hq
    refine le_trans (abs_rat_le_ceil_nat q) ?_
    have h : ⌈|(q : ℝ)|⌉₊ ≤ Qb :=
      Finset.le_sup (f := fun q : ℚ => ⌈|(q : ℝ)|⌉₊) (Finset.mem_union_left Qs₂ hq)
    exact_mod_cast h
  have hQb₂ : ∀ q ∈ Qs₂, |(q : ℝ)| ≤ (Qb : ℝ) := by
    intro q hq
    refine le_trans (abs_rat_le_ceil_nat q) ?_
    have h : ⌈|(q : ℝ)|⌉₊ ≤ Qb :=
      Finset.le_sup (f := fun q : ℚ => ⌈|(q : ℝ)|⌉₊) (Finset.mem_union_right Qs₁ hq)
    exact_mod_cast h
  -- ## 3. The constants
  let L₁n : ℕ := (4 * N₁ ^ 2 + 1) ^ N₁
  let L₂n : ℕ := (4 * N₂ ^ 2 + 1) ^ N₂
  let K₀n : ℕ := max N₁ N₂ * 2 ^ Qb
  let L₁ : ℝ := (L₁n : ℝ)
  let L₂ : ℝ := (L₂n : ℝ)
  let K₀ : ℝ := (K₀n : ℝ)
  have hL₁ge1 : 1 ≤ L₁ := by
    dsimp only [L₁, L₁n]
    have h : 1 ≤ (4 * N₁ ^ 2 + 1) ^ N₁ := one_le_pow₀ (Nat.le_add_left 1 (4 * N₁ ^ 2))
    exact_mod_cast h
  have hL₂ge1 : 1 ≤ L₂ := by
    dsimp only [L₂, L₂n]
    have h : 1 ≤ (4 * N₂ ^ 2 + 1) ^ N₂ := one_le_pow₀ (Nat.le_add_left 1 (4 * N₂ ^ 2))
    exact_mod_cast h
  have hL₁pos : 0 < L₁ := lt_of_lt_of_le one_pos hL₁ge1
  have hL₂pos : 0 < L₂ := lt_of_lt_of_le one_pos hL₂ge1
  -- ## 4. The iso-radius: definability and uniqueness
  have hRhoDef : (∅ : Set ℝ).Definable LRc (RhoFam Y K₀) := rhoFam_definable hYdef K₀
  have hRhoFun := rhoFam_fun (Y := Y) (K₀ := K₀) hfun
  obtain ⟨N_mono, B_mono, hB_mono_def, hB_mono_card, htri⟩ :=
    Work.WilC4.ulpm_mono_param hOM (RhoFam Y K₀) hRhoDef hRhoFun
  -- ## 5. The boundary families
  have hDomDef : (∅ : Set ℝ).Definable LRc (DomFam Y) := domFam_definable hYdef
  have hZeroDef : (∅ : Set ℝ).Definable LRc (ZeroFam Y) := zeroFam_definable hYdef
  obtain ⟨N_D, hPD_def, hPD_card⟩ := boundary_family (k := k) hOM hDomDef
  obtain ⟨N_Z, hPZ_def, hPZ_card⟩ := boundary_family (k := k) hOM hZeroDef
  -- ## 6. `P`
  let PD : Set (Fin (k + 1) → ℝ) :=
    {p | WilC2.IsBnd {x : ℝ | Fin.cons x (Fin.tail p) ∈ DomFam Y} (p 0)}
  let PZ : Set (Fin (k + 1) → ℝ) :=
    {p | WilC2.IsBnd {x : ℝ | Fin.cons x (Fin.tail p) ∈ ZeroFam Y} (p 0)}
  let P : Set (Fin (k + 1) → ℝ) := B_mono ∪ PD ∪ PZ
  have hPDfib : ∀ (c : Fin k → ℝ) (x : ℝ),
      Fin.cons x c ∈ PD ↔ WilC2.IsBnd (DomFib Y c) x := by
    intro c x
    simp only [PD, Set.mem_ofPred_eq, DomFam, DomFib, Fin.cons_zero, Fin.tail_cons]
  have hPZfib : ∀ (c : Fin k → ℝ) (x : ℝ),
      Fin.cons x c ∈ PZ ↔ WilC2.IsBnd (ZeroFib Y c) x := by
    intro c x
    simp only [PZ, Set.mem_ofPred_eq, ZeroFam, ZeroFib, Fin.cons_zero, Fin.tail_cons]
  have hPdef : (∅ : Set ℝ).Definable LRc P := by
    dsimp only [P, PD, PZ]
    exact (hB_mono_def.union hPD_def).union hPZ_def
  have hB_mono_sub : B_mono ⊆ P := fun p hp => Or.inl (Or.inl hp)
  have hPD_sub : PD ⊆ P := fun p hp => Or.inl (Or.inr hp)
  have hPZ_sub : PZ ⊆ P := fun p hp => Or.inr hp
  -- ## 7. The final constant
  let Ncard : ℕ := N_mono + N_D + N_Z
  let N : ℕ := max Ncard (max K₀n (2 * max L₁n L₂n))
  have hNpos : 0 < N := by
    have h1 : 0 < K₀n := by
      dsimp only [K₀n]
      have h2 : 0 < max N₁ N₂ := lt_of_lt_of_le hN₁pos (le_max_left N₁ N₂)
      positivity
    exact lt_of_lt_of_le h1 (le_trans (le_max_left _ _) (le_max_right _ _))
  have hNcard_le : Ncard ≤ N := le_max_left _ _
  have hK₀n_le : K₀n ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hL₁n_le : 2 * L₁n ≤ N := by
    have h1 : L₁n ≤ max L₁n L₂n := le_max_left _ _
    have h2 : 2 * L₁n ≤ 2 * max L₁n L₂n := Nat.mul_le_mul_left 2 h1
    have h3 : 2 * max L₁n L₂n ≤ max K₀n (2 * max L₁n L₂n) := le_max_right _ _
    have h4 : max K₀n (2 * max L₁n L₂n) ≤ N := le_max_right _ _
    exact le_trans (le_trans h2 h3) h4
  have hL₂n_le : 2 * L₂n ≤ N := by
    have h1 : L₂n ≤ max L₁n L₂n := le_max_right _ _
    have h2 : 2 * L₂n ≤ 2 * max L₁n L₂n := Nat.mul_le_mul_left 2 h1
    have h3 : 2 * max L₁n L₂n ≤ max K₀n (2 * max L₁n L₂n) := le_max_right _ _
    have h4 : max K₀n (2 * max L₁n L₂n) ≤ N := le_max_right _ _
    exact le_trans (le_trans h2 h3) h4
  have hK₀_le_N : K₀ ≤ (N : ℝ) := by
    dsimp only [K₀]; exact_mod_cast hK₀n_le
  have h2L₁_le_N : 2 * L₁ ≤ (N : ℝ) := by
    have h : ((2 * L₁n : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hL₁n_le
    push_cast at h
    simpa only [L₁] using h
  have h2L₂_le_N : 2 * L₂ ≤ (N : ℝ) := by
    have h : ((2 * L₂n : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hL₂n_le
    push_cast at h
    simpa only [L₂] using h
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  refine ⟨N, hNpos, P, hPdef, ?_⟩
  -- ## 8. The fibre cardinality bound
  intro c
  have hPfib_eq : {x : ℝ | Fin.cons x c ∈ P} =
      ({x : ℝ | Fin.cons x c ∈ B_mono} ∪ {x : ℝ | Fin.cons x c ∈ PD}) ∪
        {x : ℝ | Fin.cons x c ∈ PZ} := by
    dsimp only [P]
    exact fibre_P_eq (B_mono := B_mono) (PD := PD) (PZ := PZ) c
  have hPcard_le : {x : ℝ | Fin.cons x c ∈ P}.encard ≤ ((Ncard : ℕ) : ℕ∞) := by
    rw [hPfib_eq]
    exact encard_union3 (hB_mono_card c) (hPD_card c) (hPZ_card c)
  have hcard_cast : ((Ncard : ℕ) : ℕ∞) ≤ ((N : ℕ) : ℕ∞) := by exact_mod_cast hNcard_le
  have hPfin : ({x : ℝ | Fin.cons x c ∈ P}).Finite :=
    Set.encard_lt_top_iff.mp (lt_of_le_of_lt (le_trans hPcard_le hcard_cast)
      (WithTop.coe_lt_top N))
  refine ⟨le_trans hPcard_le hcard_cast, ?_⟩
  -- ## 9. The ball property
  intro x y₀ y hy₀ hy₀ne hclose
  by_cases hxP : Fin.cons x c ∈ P
  · -- vacuous: `p := x` gives `N|y-x| < 0`
    refine absurd (hclose x hxP) (not_lt.mpr ?_)
    simpa using mul_nonneg (Nat.cast_nonneg N) (abs_nonneg (y - x))
  · -- the real content
    obtain ⟨R, hR⟩ := hbdd c
    have hbddC : ∀ x y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y → |x| ≤ R := hR
    have hxD : x ∈ DomFib Y c := ⟨y₀, hy₀⟩
    have hxNotZ : x ∉ ZeroFib Y c := by
      rintro ⟨w, hw, hw0⟩
      exact hy₀ne (by rw [hfun c x y₀ w hy₀ hw, hw0])
    have hxnbD : ¬ WilC2.IsBnd (DomFib Y c) x := by
      intro hb
      exact hxP (Or.inl (Or.inr ((hPDfib c x).mpr hb)))
    have hbddD : ∃ R : ℝ, ∀ z ∈ DomFib Y c, |z| ≤ R :=
      ⟨R, fun z hz => by obtain ⟨w, hw⟩ := hz; exact hR z w hw⟩
    -- ## 9a. the piece
    obtain ⟨⟨a, haB, hax⟩, ⟨b, hbB, hxb⟩⟩ := exists_bnd_below_above hbddD hxD hxnbD
    have haP : Fin.cons a c ∈ P := hPD_sub ((hPDfib c a).mpr haB)
    have hbP : Fin.cons b c ∈ P := hPD_sub ((hPDfib c b).mpr hbB)
    obtain ⟨p₁, p₂, hp₁P, hp₂P, hp₁x, hxp₂, hsep, hdistle, hdistmin⟩ :=
      piece_adjacent hPfin hxP ⟨a, haP, hax⟩ ⟨b, hbP, hxb⟩
    have hp₁p₂ : p₁ < p₂ := lt_trans hp₁x hxp₂
    -- ## 9b. the piece is contained in the fibre where the value is nonzero
    have hsepD : ∀ z ∈ Set.Ioo p₁ p₂, ¬ WilC2.IsBnd (DomFib Y c) z := by
      intro z hz hb
      exact hsep z (hPD_sub ((hPDfib c z).mpr hb)) hz.1 hz.2
    have hsepZ : ∀ z ∈ Set.Ioo p₁ p₂, ¬ WilC2.IsBnd (ZeroFib Y c) z := by
      intro z hz hb
      exact hsep z (hPZ_sub ((hPZfib c z).mpr hb)) hz.1 hz.2
    have hpieceD : Set.Ioo p₁ p₂ ⊆ DomFib Y c := piece_subset_of_notBnd hp₁x hxp₂ hsepD hxD
    have hpieceZ : Set.Ioo p₁ p₂ ⊆ (ZeroFib Y c)ᶜ :=
      piece_subset_of_notBnd hp₁x hxp₂
        (fun z hz hb => hsepZ z hz ((WilC2.isBnd_compl (D := ZeroFib Y c)).mp hb)) hxNotZ
    have hpieceV : Set.Ioo p₁ p₂ ⊆ ValFib Y c := by
      intro z hz
      obtain ⟨w, hw⟩ := hpieceD hz
      exact ⟨w, hw, fun hw0 => hpieceZ hz ⟨w, hw, hw0⟩⟩
    -- ## 9c. the iso-radius as a function
    let ρ : ℝ → ℝ := fun z => if h : ∃ q : ℝ, RhoVal Y K₀ c z q then Classical.choose h else 0
    have hρ_mem : ∀ z : ℝ, (∃ q : ℝ, RhoVal Y K₀ c z q) → RhoVal Y K₀ c z (ρ z) := by
      intro z hz
      dsimp only [ρ]
      rw [dif_pos hz]
      exact Classical.choose_spec hz
    have hρ_val : ∀ z ∈ ValFib Y c, RhoVal Y K₀ c z (ρ z) := by
      intro z hz
      obtain ⟨y', hy'mem, hy'ne⟩ := hz
      obtain ⟨q, hq, -⟩ := rho_exists_unique (Y := Y) (K₀ := K₀) hfun hbddC hy'mem hy'ne
      exact hρ_mem z ⟨q, hq⟩
    -- ## 9d. monotonicity of `ρ` on the piece
    have htri_piece : ∀ x₁ x₂ x₃ : ℝ, x₁ ∈ Set.Ioo p₁ p₂ → x₂ ∈ Set.Ioo p₁ p₂ →
        x₃ ∈ Set.Ioo p₁ p₂ → x₁ < x₂ → x₂ < x₃ →
        (ρ x₁ ≤ ρ x₂ ∧ ρ x₂ ≤ ρ x₃) ∨ (ρ x₃ ≤ ρ x₂ ∧ ρ x₂ ≤ ρ x₁) := by
      intro x₁ x₂ x₃ h1 h2 h3 hl12 hl23
      have hfree : ∀ z ∈ Set.Ioo p₁ p₂, Fin.cons z c ∉ B_mono := by
        intro z hz hzB
        exact hsep z (hB_mono_sub hzB) hz.1 hz.2
      exact htri c p₁ p₂ hp₁p₂ hfree x₁ x₂ x₃ (ρ x₁) (ρ x₂) (ρ x₃) h1 h2 h3 hl12 hl23
        ((rhoFam_mem_iff (Y := Y) (K₀ := K₀) x₁ (ρ x₁) c).mpr (hρ_val x₁ (hpieceV h1)))
        ((rhoFam_mem_iff (Y := Y) (K₀ := K₀) x₂ (ρ x₂) c).mpr (hρ_val x₂ (hpieceV h2)))
        ((rhoFam_mem_iff (Y := Y) (K₀ := K₀) x₃ (ρ x₃) c).mpr (hρ_val x₃ (hpieceV h3)))
    have hmono_anti := Work.WilC4.mono_of_three_point (f := ρ) hp₁p₂ htri_piece
    -- ## 9e. the ULPM windows in the recentred coordinates
    have hU₁p := hU₁ p₁ c
    have hU₂p := hU₂ p₂ c
    have hdom1 : ∀ t : ℝ, 0 < t → t ≤ (p₂ - p₁) / 2 → p₁ + 1 * t ∈ DomFib Y c := by
      intro t ht htS
      exact hpieceD ⟨by linarith, by linarith⟩
    have hdom2 : ∀ t : ℝ, 0 < t → t ≤ (p₂ - p₁) / 2 → p₂ + (-1) * t ∈ DomFib Y c := by
      intro t ht htS
      exact hpieceD ⟨by linarith, by linarith⟩
    have hsub1 : (N₁ : ℝ) * 2 ^ Qb ≤ K₀ := by
      have h2Qb : (0 : ℝ) ≤ 2 ^ Qb := by positivity
      have hmax : (N₁ : ℝ) ≤ (max N₁ N₂ : ℝ) := by exact_mod_cast le_max_left N₁ N₂
      have h : ((N₁ * 2 ^ Qb : ℕ) : ℝ) ≤ (K₀n : ℝ) := by
        dsimp only [K₀n]
        push_cast
        exact mul_le_mul_of_nonneg_right hmax h2Qb
      have hK₁ : ((N₁ * 2 ^ Qb : ℕ) : ℝ) = (N₁ : ℝ) * 2 ^ Qb := by push_cast; ring
      rw [hK₁] at h
      simpa only [K₀] using h
    have hsub2 : (N₂ : ℝ) * 2 ^ Qb ≤ K₀ := by
      have h2Qb : (0 : ℝ) ≤ 2 ^ Qb := by positivity
      have hmax : (N₂ : ℝ) ≤ (max N₁ N₂ : ℝ) := by exact_mod_cast le_max_right N₁ N₂
      have h : ((N₂ * 2 ^ Qb : ℕ) : ℝ) ≤ (K₀n : ℝ) := by
        dsimp only [K₀n]
        push_cast
        exact mul_le_mul_of_nonneg_right hmax h2Qb
      have hK₂ : ((N₂ * 2 ^ Qb : ℕ) : ℝ) = (N₂ : ℝ) * 2 ^ Qb := by push_cast; ring
      rw [hK₂] at h
      simpa only [K₀] using h
    have hLeq₁ : L₁ = (4 * (N₁ : ℝ) ^ 2 + 1) ^ N₁ := by
      dsimp only [L₁, L₁n]
      push_cast
      ring
    have hLeq₂ : L₂ = (4 * (N₂ : ℝ) ^ 2 + 1) ^ N₂ := by
      dsimp only [L₂, L₂n]
      push_cast
      ring
    have hwin1 : ∀ t : ℝ, 0 < t → t ≤ (p₂ - p₁) / 2 →
        ∃ t' : ℝ, t / L₁ ≤ t' ∧ t' ≤ t ∧ t' / 2 ≤ ρ (p₁ + t') := by
      intro t ht htS
      obtain ⟨t', ht'1, ht'2, hgood⟩ :=
        window_rho_lower (K₀ := (N₁ : ℝ) * 2 ^ Qb) (σ := 1) (p := p₁) (c := c)
          (N := N₁) (Qb := Qb) (Qs := Qs₁) (B := B₁) (L := L₁) (S := p₂ - p₁)
          hfun (Or.inl rfl) hN₁pos hQb₁ (hB₁card (Fin.cons p₁ c)) rfl hU₁p hLeq₁
          (by linarith [hp₁p₂]) hdom1 t ht htS
      refine ⟨t', ht'1, ht'2, ?_⟩
      have ht'pos : 0 < t' := lt_of_lt_of_le (div_pos ht hL₁pos) ht'1
      have hmem : p₁ + t' ∈ ValFib Y c := hpieceV ⟨by linarith, by linarith⟩
      obtain ⟨z₀, hz₀, hz₀ne, -⟩ := hρ_val (p₁ + t') hmem
      have hg : IsoGood Y ((N₁ : ℝ) * 2 ^ Qb) c (p₁ + t') z₀ (t' / 2) := by
        simpa only [one_mul] using hgood z₀ (by simpa only [one_mul] using hz₀)
      exact le_rho_of_isoGood hfun hz₀ (hρ_val (p₁ + t') hmem) (by linarith)
        (IsoGood_mono_factor (K := (N₁ : ℝ) * 2 ^ Qb) (K' := K₀) hg hsub1)
    have hwin2 : ∀ t : ℝ, 0 < t → t ≤ (p₂ - p₁) / 2 →
        ∃ t' : ℝ, t / L₂ ≤ t' ∧ t' ≤ t ∧ t' / 2 ≤ ρ (p₂ - t') := by
      intro t ht htS
      obtain ⟨t', ht'1, ht'2, hgood⟩ :=
        window_rho_lower (K₀ := (N₂ : ℝ) * 2 ^ Qb) (σ := -1) (p := p₂) (c := c)
          (N := N₂) (Qb := Qb) (Qs := Qs₂) (B := B₂) (L := L₂) (S := p₂ - p₁)
          hfun (Or.inr rfl) hN₂pos hQb₂ (hB₂card (Fin.cons p₂ c)) rfl hU₂p hLeq₂
          (by linarith [hp₁p₂]) hdom2 t ht htS
      refine ⟨t', ht'1, ht'2, ?_⟩
      have ht'pos : 0 < t' := lt_of_lt_of_le (div_pos ht hL₂pos) ht'1
      have hmem : p₂ - t' ∈ ValFib Y c := hpieceV ⟨by linarith, by linarith⟩
      obtain ⟨z₀, hz₀, hz₀ne, -⟩ := hρ_val (p₂ - t') hmem
      have hg : IsoGood Y ((N₂ : ℝ) * 2 ^ Qb) c (p₂ - t') z₀ (t' / 2) := by
        simpa only [neg_one_mul, sub_eq_add_neg] using hgood z₀ (by simpa only [neg_one_mul, sub_eq_add_neg] using hz₀)
      exact le_rho_of_isoGood hfun hz₀ (hρ_val (p₂ - t') hmem) (by linarith)
        (IsoGood_mono_factor (K := (N₂ : ℝ) * 2 ^ Qb) (K' := K₀) hg hsub2)
    -- ## 9f. `ρ(x) ≥ dist(x,P)/N`
    have hxIoo : x ∈ Set.Ioo p₁ p₂ := ⟨hp₁x, hxp₂⟩
    have hxb : 0 ≤ min (x - p₁) (p₂ - x) := le_of_lt (lt_min (by linarith) (by linarith))
    have hlow : min (x - p₁) (p₂ - x) / (N : ℝ) ≤ ρ x := by
      rcases hmono_anti with hmono | hanti
      · have hb := piece_lower_mono (ρ := ρ) hp₁p₂ hL₁ge1 hmono hwin1 x hxIoo
        have hmon : min (x - p₁) (p₂ - x) / (N : ℝ) ≤
            min (x - p₁) (p₂ - x) / (2 * L₁) :=
          div_le_div_of_nonneg_left hxb (by linarith [hL₁pos]) h2L₁_le_N
        linarith
      · have hb := piece_lower_anti (ρ := ρ) hp₁p₂ hL₂ge1 hanti hwin2 x hxIoo
        have hmon : min (x - p₁) (p₂ - x) / (N : ℝ) ≤
            min (x - p₁) (p₂ - x) / (2 * L₂) :=
          div_le_div_of_nonneg_left hxb (by linarith [hL₂pos]) h2L₂_le_N
        linarith
    -- ## 9g. the distance comparison
    have hNy : (N : ℝ) * |y - x| < min (x - p₁) (p₂ - x) := by
      rcases hdistmin with h | h
      · rw [h]; exact hclose p₁ hp₁P
      · rw [h]; exact hclose p₂ hp₂P
    have hyx_lt : |y - x| < ρ x := by
      have h1 : |y - x| < min (x - p₁) (p₂ - x) / (N : ℝ) := by
        rw [lt_div_iff₀ hNposR]
        linarith [hNy]
      linarith
    -- ## 9h. the good ball at `x`
    have hρx : RhoVal Y K₀ c x (ρ x) := hρ_val x ⟨y₀, hy₀, hy₀ne⟩
    have hrpos : 0 ≤ (|y - x| + ρ x) / 2 := by
      have h : 0 < ρ x := lt_of_le_of_lt (abs_nonneg (y - x)) hyx_lt
      linarith [abs_nonneg (y - x)]
    have hgoodr : IsoGood Y K₀ c x y₀ ((|y - x| + ρ x) / 2) :=
      isoGood_of_lt_rho hfun hy₀ hρx hrpos (by linarith)
    obtain ⟨y₁, hy₁, hb1, hb2⟩ := hgoodr y (by linarith)
    exact ⟨y₁, hy₁, le_trans hb1 (mul_le_mul_of_nonneg_right hK₀_le_N (abs_nonneg y₀)),
      le_trans hb2 (mul_le_mul_of_nonneg_right hK₀_le_N (abs_nonneg y₁))⟩

end Work.WilVP
