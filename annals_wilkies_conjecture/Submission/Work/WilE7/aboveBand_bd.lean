/-
  WilE7 (`Submission.Work.WilE7.aboveBand_bd`): the *open above band* of the top sheet is a
  **single** `*`-piece with format and degree bounds polynomial in the input data.

  This is the bounded companion of `Work.WilE7.AboveAux.aboveBand_star` (which produces a `Star`,
  i.e. a *list* of pieces, without controlling their complexity).  The induction of
  `Submission/Work/WilE7/E7main_DESIGN.md` consumes the *piece* itself: the cell of the cylindrical
  decomposition has to be the projection of *one* connected component.

  The construction is the fibre product `Z ×_{ℝ^p} S.X` with a vertical coordinate, cut by
  `v₂ < t < 1` (`Work.WilE7.AboveAux.aboveBandS`); the connected component of that set through the
  canonical interior point `aboveBandPt` projects exactly onto the band
  (`aboveBandComp_sub_aux` / `aboveBandComp_cov_aux`).  The file

  * `aboveBandS_fmt_le`, `aboveBandS_deg_le`: format and degree of `aboveBandS` in terms of the
    formats and degrees of `Z` and `S.X`;
  * `aboveBandStar_piece`: the single piece, with those explicit bounds;
  * `aboveBand_bd`: the packaged form — there are `A` (depending only on `F`) and a polynomial
    `Cb` (depending only on `F`) with `X.fmt ≤ A` and `X.deg ≤ Cb.eval D` whenever
    `S.X.fmt ≤ F`, `Z.fmt ≤ F`, `S.deg ≤ D`, `Z.deg ≤ D`.
-/
import Mathlib
import Submission.Work.WilE7.aboveCell_star_open
import Submission.Work.WilE7.BelowAux.belowStarPiece_extract

set_option autoImplicit false
-- the hypotheses of the target live inside the `∀` of an `∃ … ∀ …` statement; the unused-variable
-- linter mis-reports such binders, which cannot be renamed without changing the statement
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## Format/degree bookkeeping for the presentation `aboveBandS` -/

/-- The vertical cube has degree `0`. -/
theorem bandCube1_deg : bandCube1.deg = 0 := by
  simp [bandCube1, Work.WilE8.cubeSemiPf, WilkiesDesign.E.SemiPf.deg,
    WilkiesDesign.E.Basic.deg]

/-- The vertical cube has format `1`. -/
theorem bandCube1_fmt : bandCube1.fmt = 1 := by
  simp [bandCube1, Work.WilE8.cubeSemiPf, WilkiesDesign.E.SemiPf.fmt]

/-- The format of a fibre product is the sum of the formats of the factors. -/
theorem fiberProdZ_fmt_eq {p q : ℕ} (X X' : SemiPf (p + q)) :
    (fiberProdZ X X').fmt = X.fmt + X'.fmt := by
  simp only [WilkiesDesign.E.SemiPf.fmt, fiberProdZ]
  ring

/-- The format of a product is the sum of the formats of the factors. -/
theorem prod_fmt_eq {k k' : ℕ} (X : SemiPf k) (X' : SemiPf k') :
    (SemiPf.prod X X').fmt = X.fmt + X'.fmt := by
  simp only [WilkiesDesign.E.SemiPf.fmt, SemiPf.prod_r]
  ring

/-- **Format of `aboveBandS`.** -/
theorem aboveBandS_fmt_le {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    (AboveAux.aboveBandS Z S).fmt ≤ 2 * max S.X.fmt Z.fmt + 1 := by
  have h1 : (AboveAux.aboveBandS Z S).fmt = (AboveAux.abovePadded Z S).fmt :=
    SemiPf.addConds_fmt (AboveAux.abovePadded Z S) []
      [AboveAux.abovePlow p m (AboveAux.abovePadded Z S).r,
       AboveAux.abovePtop p m (AboveAux.abovePadded Z S).r]
  have h2 : (AboveAux.abovePadded Z S).fmt =
      (AboveAux.aboveW1 Z S).fmt + bandCube1.fmt :=
    prod_fmt_eq (AboveAux.aboveW1 Z S) bandCube1
  have h3 : (AboveAux.aboveW1 Z S).fmt = Z.fmt + S.X.fmt :=
    fiberProdZ_fmt_eq Z S.X
  rw [h1, h2, h3, bandCube1_fmt]
  have h4 := le_max_left S.X.fmt Z.fmt
  have h5 := le_max_right S.X.fmt Z.fmt
  omega

/-- Elementary arithmetic: `d + max 1 d * 4 ≤ 5 * (1 + d)`. -/
theorem deg_addConds_arith (d : ℕ) : d + max 1 d * 4 ≤ 5 * (1 + d) := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; norm_num
  · have hm : max 1 d = d := max_eq_right h
    rw [hm]; omega

/-- **Degree of `aboveBandS`.**  The bound is
`5 (1 + 2 (1 + 2 (1 + max F_z F_s) (1 + (deg Z + deg S.X))²)²)`, i.e. it is obtained by
chaining the fibre-product, product and `addConds` estimates. -/
theorem aboveBandS_deg_le {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    (AboveAux.aboveBandS Z S).deg ≤
      5 * (1 + 2 * (1 + 2 * (1 + max S.X.fmt Z.fmt) * (1 + (Z.deg + S.X.deg)) ^ 2) ^ 2) := by
  have hZF : Z.fmt ≤ max S.X.fmt Z.fmt := le_max_right _ _
  -- degree of the fibre product
  have hW : (AboveAux.aboveW1 Z S).deg ≤
      2 * (1 + max S.X.fmt Z.fmt) * (1 + (Z.deg + S.X.deg)) ^ 2 :=
    fiberProdZ_deg Z S.X hZF
  -- degree of the padded product
  have hP : (AboveAux.abovePadded Z S).deg ≤
      2 * (1 + 2 * (1 + max S.X.fmt Z.fmt) * (1 + (Z.deg + S.X.deg)) ^ 2) ^ 2 := by
    have h1 : (AboveAux.abovePadded Z S).deg ≤ 2 * (1 + (AboveAux.aboveW1 Z S).deg) ^ 2 := by
      calc (AboveAux.abovePadded Z S).deg
          = (SemiPf.prod (AboveAux.aboveW1 Z S) bandCube1).deg := rfl
        _ ≤ 2 * (1 + ((AboveAux.aboveW1 Z S).deg + bandCube1.deg)) ^ 2 :=
            prodDeg (AboveAux.aboveW1 Z S) bandCube1
        _ = 2 * (1 + (AboveAux.aboveW1 Z S).deg) ^ 2 := by rw [bandCube1_deg, Nat.add_zero]
    have hle : 1 + (AboveAux.aboveW1 Z S).deg ≤
        1 + 2 * (1 + max S.X.fmt Z.fmt) * (1 + (Z.deg + S.X.deg)) ^ 2 := by
      omega
    exact le_trans h1 (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hle 2))
  -- degree of the cut
  have hB := SemiPf.addConds_deg_le (AboveAux.abovePadded Z S) []
    [AboveAux.abovePlow p m (AboveAux.abovePadded Z S).r,
     AboveAux.abovePtop p m (AboveAux.abovePadded Z S).r]
  have hsum : (([] : List (EAPoly (BelowAux.belowDim p m) (AboveAux.abovePadded Z S).r)).map
        atomDeg).sum +
      ([AboveAux.abovePlow p m (AboveAux.abovePadded Z S).r,
        AboveAux.abovePtop p m (AboveAux.abovePadded Z S).r].map atomDeg).sum ≤ 4 := by
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero]
    have h1 := AboveAux.atomDeg_abovePlow (p := p) (m := m) (r := (AboveAux.abovePadded Z S).r)
    have h2 := AboveAux.atomDeg_abovePtop (p := p) (m := m) (r := (AboveAux.abovePadded Z S).r)
    omega
  have hstep : (AboveAux.abovePadded Z S).deg + max 1 (AboveAux.abovePadded Z S).deg * 4 ≤
      5 * (1 + (AboveAux.abovePadded Z S).deg) := deg_addConds_arith _
  have hfinal : 5 * (1 + (AboveAux.abovePadded Z S).deg) ≤
      5 * (1 + 2 * (1 + 2 * (1 + max S.X.fmt Z.fmt) * (1 + (Z.deg + S.X.deg)) ^ 2) ^ 2) :=
    Nat.mul_le_mul_left 5 (by omega)
  refine le_trans hB (le_trans ?_ hfinal)
  exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hsum) _) hstep

/-! ## The single `*`-piece -/

/-- **The open above band of the top sheet is a single `*`-piece.**

The piece is the reindexed presentation `aboveBandS Z S` based at the canonical interior point
`aboveBandPt`; the two inclusions `aboveBandComp_sub_aux` / `aboveBandComp_cov_aux` show that its
connected component projects exactly onto the band. -/
theorem aboveBandStar_piece
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    ∃ P : WilkiesDesign.E.StarPiece (p + 1),
      P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1} ∧
      P.X.fmt ≤ 2 * max S.X.fmt Z.fmt + 1 ∧
      P.X.deg ≤ 5 * (1 + 2 * (1 + 2 * (1 + max S.X.fmt Z.fmt) * (1 + (Z.deg + S.X.deg)) ^ 2) ^ 2) := by
  classical
  -- the canonical point of the band and the component through it
  set p₀ : Fin (BelowAux.belowDim p m) → ℝ := AboveAux.aboveBandPt u₀ s hk with hp₀def
  have hp₀ : p₀ ∈ (AboveAux.aboveBandS Z S).set := by
    rw [hp₀def]
    exact AboveAux.aboveBandPt_mem S Z u₀ hu₀ C hC k hk s hsub hgt
  set O : Set (Fin (BelowAux.belowDim p m) → ℝ) :=
    connectedComponentIn (AboveAux.aboveBandS Z S).set p₀ with hOdef
  -- the coordinate permutation and the piece
  obtain ⟨e, he⟩ := BelowAux.belowPerm p m
  have he' : ∀ y : Fin ((p + 1) + BelowAux.belowFib p m) → ℝ,
      WilkiesDesign.E.projFirst (p + 1) (BelowAux.belowFib p m) y =
        BelowAux.belowExtract (fun i => y (e i)) := fun y => he y
  set P : WilkiesDesign.E.StarPiece (p + 1) :=
    ⟨BelowAux.belowFib p m, Work.WilE7.SemiPf.reindex e (AboveAux.aboveBandS Z S),
      (Work.WilE7.pullHomeo e).symm p₀⟩ with hPdef
  have hPset : P.set = BelowAux.belowExtract '' O := by
    rw [hPdef, hOdef]
    exact BelowAux.belowStarPiece_extract (X := AboveAux.aboveBandS Z S) (q := p₀) e he'
  -- the two halves of "the component projects exactly onto the band"
  have hOsub : BelowAux.belowExtract '' O ⊆
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1} := by
    have h := AboveAux.aboveBandComp_sub_aux S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hgt
    simpa only [hOdef, hp₀def] using h
  have hOsup :
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1} ⊆ BelowAux.belowExtract '' O := by
    have h := AboveAux.aboveBandComp_cov_aux S Z u₀ hu₀ C hC k hk s hcont hsub hgt
    simpa only [hOdef, hp₀def] using h
  have hY : BelowAux.belowExtract '' O =
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1} := Set.Subset.antisymm hOsub hOsup
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hPset, hY]
  · rw [hPdef]
    show (Work.WilE7.SemiPf.reindex e (AboveAux.aboveBandS Z S)).fmt ≤ 2 * max S.X.fmt Z.fmt + 1
    rw [AboveAux.aboveBandS_reindex_fmt]
    exact aboveBandS_fmt_le Z S
  · rw [hPdef]
    show (Work.WilE7.SemiPf.reindex e (AboveAux.aboveBandS Z S)).deg ≤ _
    rw [Work.WilE7.sp_reindex_deg]
    exact aboveBandS_deg_le Z S

/-! ## The polynomial arithmetic of the packaging -/

/-- The composite degree bound, in terms of the format bound `F` and the degree bound `D`. -/
theorem aboveBand_deg_arith (F D DF DD : ℕ) (hDF : DF ≤ F) (hDD : DD ≤ 2 * D) :
    5 * (1 + 2 * (1 + 2 * (1 + DF) * (1 + DD) ^ 2) ^ 2)
      ≤ 5 * (1 + 2 * (2 * F + 3) ^ 2) * (1 + 2 * D) ^ 4 := by
  set e := 1 + 2 * D with he
  have he1 : 1 ≤ e := by omega
  have he1sq : 1 ≤ e ^ 2 := one_le_pow₀ he1
  have he4 : 1 ≤ e ^ 4 := one_le_pow₀ he1
  have hDF1 : 1 + DF ≤ 1 + F := by omega
  have hDD1 : 1 + DD ≤ e := by omega
  have hsq : (1 + DD) ^ 2 ≤ e ^ 2 := Nat.pow_le_pow_left hDD1 2
  have hmul : (1 + DF) * (1 + DD) ^ 2 ≤ (1 + F) * e ^ 2 := Nat.mul_le_mul hDF1 hsq
  -- step 1: the inner bracket is bounded by `(2F+3) e²`
  have hstep1 : 1 + 2 * (1 + DF) * (1 + DD) ^ 2 ≤ (2 * F + 3) * e ^ 2 := by
    have h2 : 2 * ((1 + DF) * (1 + DD) ^ 2) ≤ 2 * ((1 + F) * e ^ 2) :=
      Nat.mul_le_mul_left 2 hmul
    have h3 : 1 + 2 * ((1 + DF) * (1 + DD) ^ 2) ≤ e ^ 2 + 2 * ((1 + F) * e ^ 2) :=
      Nat.add_le_add he1sq h2
    have h4 : e ^ 2 + 2 * ((1 + F) * e ^ 2) = (2 * F + 3) * e ^ 2 := by ring
    have h5 : 2 * ((1 + DF) * (1 + DD) ^ 2) = 2 * (1 + DF) * (1 + DD) ^ 2 := by ring
    rw [h5, h4] at h3
    exact h3
  -- step 2: square and add `1`
  have hstep2 : 1 + 2 * (1 + 2 * (1 + DF) * (1 + DD) ^ 2) ^ 2 ≤
      (1 + 2 * (2 * F + 3) ^ 2) * e ^ 4 := by
    have hsq2 : (1 + 2 * (1 + DF) * (1 + DD) ^ 2) ^ 2 ≤ ((2 * F + 3) * e ^ 2) ^ 2 :=
      Nat.pow_le_pow_left hstep1 2
    have hK2 : ((2 * F + 3) * e ^ 2) ^ 2 = (2 * F + 3) ^ 2 * e ^ 4 := by ring
    have hA : 2 * (1 + 2 * (1 + DF) * (1 + DD) ^ 2) ^ 2 ≤
        2 * ((2 * F + 3) ^ 2 * e ^ 4) := by
      rw [hK2] at hsq2
      exact Nat.mul_le_mul_left 2 hsq2
    calc 1 + 2 * (1 + 2 * (1 + DF) * (1 + DD) ^ 2) ^ 2
        ≤ 1 + 2 * ((2 * F + 3) ^ 2 * e ^ 4) := Nat.add_le_add_left hA 1
      _ ≤ e ^ 4 + 2 * ((2 * F + 3) ^ 2 * e ^ 4) := Nat.add_le_add_right he4 _
      _ = (1 + 2 * (2 * F + 3) ^ 2) * e ^ 4 := by ring
  calc 5 * (1 + 2 * (1 + 2 * (1 + DF) * (1 + DD) ^ 2) ^ 2)
      ≤ 5 * ((1 + 2 * (2 * F + 3) ^ 2) * e ^ 4) := Nat.mul_le_mul_left 5 hstep2
    _ = 5 * (1 + 2 * (2 * F + 3) ^ 2) * (1 + 2 * D) ^ 4 := by rw [he]; ring

/-! ## The target -/

theorem aboveBand_bd (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ), ∀ (p m : ℕ) (S : WilkiesDesign.E.Stratum p (m + 1))
      (hGood : S.Good) (hj : S.j = m + 1)
      (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
      (C : Set (Fin p → ℝ))
      (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
      (hCpf : WilkiesDesign.E.SubPf p C)
      (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
      (hcont : ∀ j, ContinuousOn (s j) C)
      (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
      (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
      (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
        ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
          WilkiesDesign.E.projSnd p (m + 1) z)
      (hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber S.X.set x).ncard = k)
      (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m))
      (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) (D : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      ∃ P : WilkiesDesign.E.StarPiece (p + 1),
        P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < 1} ∧
        P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D := by
  refine ⟨2 * F + 1, Polynomial.C (5 * (1 + 2 * (2 * F + 3) ^ 2)) *
    (1 + 2 * Polynomial.X) ^ 4, ?_⟩
  intro p m S hGood hj Z u₀ hu₀ C hC hCpf k hk s hcont hinj hsub hcov hcard hlvl hgt D
    hSF hSD hZF hZD
  obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
    aboveBandStar_piece S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hgt
  refine ⟨P, hPset, ?_, ?_⟩
  · -- format: `max S.X.fmt Z.fmt ≤ F`
    have hmax : max S.X.fmt Z.fmt ≤ F := max_le hSF hZF
    omega
  · -- degree: assemble the polynomial arithmetic
    have hDval : (Polynomial.C (5 * (1 + 2 * (2 * F + 3) ^ 2)) *
        (1 + 2 * Polynomial.X) ^ 4 : Polynomial ℕ).eval D
        = 5 * (1 + 2 * (2 * F + 3) ^ 2) * (1 + 2 * D) ^ 4 := by simp
    rw [hDval]
    have hDF : max S.X.fmt Z.fmt ≤ F := max_le hSF hZF
    have hDD : Z.deg + S.X.deg ≤ 2 * D := by
      have hSXd : S.X.deg ≤ S.deg := Nat.le_add_right _ _
      omega
    exact le_trans hPdeg (aboveBand_deg_arith F D (max S.X.fmt Z.fmt) (Z.deg + S.X.deg) hDF hDD)

end Work.WilE7
