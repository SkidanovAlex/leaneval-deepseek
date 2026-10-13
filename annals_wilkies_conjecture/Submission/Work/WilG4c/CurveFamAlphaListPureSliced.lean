/-
  WilG4c — `CurveFamAlphaListPureSliced`: the **fibre** (sliced) form of the pure
  near-maximising `γ`-selection of BNZ §5.4.

  This is `Work.WilG4c.CurveFamAlpha_list_pure` with the *joint* locus `AlLoc` (the interior of
  the `C^{|L|}`-locus of `famFunHat f`) replaced by the *fibre* locus `SliceLocus p n f |L|`
  (smoothness of the slice `u ↦ f l u` at the cube point), the *joint* derivative graph
  `AlDgList` replaced by the *slice* derivative graph `AlDgListSlice`, and the joint iterated
  directional derivative `iterDir (liftDir L) (famFunHat f) (xPt l x y)` replaced by the honest
  fibre derivative

      `iteratedFDeriv ℝ |L| (fun u => f l u) (pt x y) (fun j => Pi.single (L.get j) 1)`.

  The whole analytic content sits in the `Ω`-definability of `AlDgListSlice`
  (`Work.WilG4c.AlDgListSliceMem`); the rest is the verbatim `Ω`-bookkeeping of
  `CurveFamAlphaDefs`/`Alpha/AlphaViolMem`/`CurveFamAlpha_list_pure` with the new atom.  The
  helpers below are the fibre analogues of `AlphaViolIff` and of
  `mem_AlZsetPure_liftDir_iff`: they unfold membership in `AlViolSlice`/`AlZsetPureSlice` at a
  point `xPt l x y` into exactly the hypothesis/conclusion of the statement.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedAlpha
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.CurveFamAlpha_list_pure
import Submission.Work.WilG4c.AlDgListSliceMem
import Submission.Work.WilG4c.AlZsetPureSliceMem
import Submission.Work.WilG4c.Hyps

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c
open Work.WilG5

namespace SliceChoiceAux

open Work.WilG4c.CurveFam

/-- The `L`-th iterated directional derivative of the *slice* `u ↦ f (parPt w) u` at the cube
point `cubePt w`: the value stored in the last coordinate of `AlDgListSlice p n f L`. -/
noncomputable def sliceDg {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) (w : Fin (p + (n + 1)) → ℝ) : ℝ :=
  iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f (parPt w) u) (cubePt w)
    (fun j => Pi.single (L.get j) 1)

/-- The parameter of `xPt l x y` is `l`. -/
theorem parPt_xPt {p n : ℕ} (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    parPt (xPt l x y) = l := by
  funext i
  simp only [parPt, xPt, Fin.append_left]

/-- The cube point of `xPt l x y` is `pt x y`. -/
theorem cubePt_xPt {p n : ℕ} (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    cubePt (xPt l x y) = pt x y := by
  funext j
  simp only [cubePt, xPt, pt, Fin.append_right]

/-- Membership of `xPt l x y` in the fibre `C^k`-locus: it is exactly the `C^k`-smoothness of
the slice `u ↦ f l u` at `pt x y`. -/
theorem mem_SliceLocus_xPt {p n k : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    xPt l x y ∈ SliceLocus p n f k ↔
      ContDiffAt ℝ k (fun u : Fin (n + 1) → ℝ => f l u) (pt x y) := by
  simp only [SliceLocus, Set.mem_ofPred_eq, parPt_xPt, cubePt_xPt]

/-- Membership of `Fin.snoc w s` in the slice derivative graph, in `sliceDg` form. -/
theorem snoc_mem_AlDgListSlice {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (n + 1))} {w : Fin (p + (n + 1)) → ℝ} {s : ℝ} :
    Fin.snoc w s ∈ AlDgListSlice p n f L ↔ w ∈ SliceLocus p n f L.length ∧ s = sliceDg f L w := by
  rw [mem_AlDgListSlice, Fin.init_snoc, Fin.snoc_last]
  simp only [SliceLocus, Set.mem_ofPred_eq, sliceDg]

/-- **The fibre violation set, unfolded.**  `w` is beaten on the fibre iff some cube point
`y'` of the same slice, at which the slice is `C^{|L|}`, has a strictly larger `|∂^L|`.

This is the `AlDgListSlice`/`SliceLocus` version of `Alpha/AlphaViolIff`. -/
theorem alphaViolSlice_iff {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) (w : Fin (p + (n + 1)) → ℝ) :
    w ∈ AlViolSlice p n f L ↔ w ∈ SliceLocus p n f L.length ∧
      ∃ y' : Fin n → ℝ, y' ∈ openCube n ∧
        zPt p n w y' ∈ SliceLocus p n f L.length ∧
        2 * |sliceDg f L w| < |sliceDg f L (zPt p n w y')| := by
  constructor
  · intro hw
    rw [AlViolSlice, projN, Set.mem_ofPred_eq] at hw
    obtain ⟨v, hv⟩ := hw
    rw [AlViolSlice1, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff] at hv
    obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := hv
    have hA₁ : Fin.snoc w (v (blkS n)) ∈ AlDgListSlice p n f L := by
      rw [← comp_iwIdx (p := p) (n := n) w v]
      exact hA
    have hA₂ := snoc_mem_AlDgListSlice.mp hA₁
    have hB₁ : Fin.snoc ((Fin.append w v) ∘ (zIdx p n)) (v (Fin.last (n + 1)))
        ∈ AlDgListSlice p n f L := by
      rw [← comp_izIdx (p := p) (n := n) w v]
      exact hB
    have hB₂ : zPt p n w (fun j : Fin n => v (Fin.castAdd 2 j)) ∈ SliceLocus p n f L.length ∧
        v (Fin.last (n + 1)) =
          sliceDg f L (zPt p n w (fun j : Fin n => v (Fin.castAdd 2 j))) := by
      have h := hB₁
      rw [comp_zIdx (p := p) (n := n) w v] at h
      exact snoc_mem_AlDgListSlice.mp h
    have hC₁ : (Fin.cons (v (blkS n)) (fun _ : Fin 1 => v (Fin.last (n + 1))) : Fin 2 → ℝ)
        ∈ cmpSet := by
      rw [← comp_icIdx (p := p) (n := n) w v]
      exact hC
    have hC₂ : 2 * |v (blkS n)| < |v (Fin.last (n + 1))| := by
      have h := (Work.WilG4c.Alpha.mem_cmpSet_iff
        (Fin.cons (v (blkS n)) (fun _ : Fin 1 => v (Fin.last (n + 1))))).mp hC₁
      simpa using h
    have hD₁ : (fun j : Fin n => v (Fin.castAdd 2 j)) ∈ openCube n := by
      rw [← comp_cubeIdx (p := p) (n := n) w v]
      exact hD
    refine ⟨hA₂.1, fun j : Fin n => v (Fin.castAdd 2 j), hD₁, hB₂.1, ?_⟩
    rw [← hA₂.2, ← hB₂.2]
    exact hC₂
  · rintro ⟨hLW, y', hy', hLZ, hineq⟩
    set u : Fin 2 → ℝ :=
      Fin.cons (sliceDg f L w) (fun _ : Fin 1 => sliceDg f L (zPt p n w y')) with hu
    have hblk : (Fin.append y' u) (blkS n) = sliceDg f L w := by
      rw [hu]; exact append_blkS y' u
    have hlast : (Fin.append y' u) (Fin.last (n + 1)) = sliceDg f L (zPt p n w y') := by
      rw [hu]; exact append_last y' u
    refine ⟨Fin.append y' u, ?_⟩
    rw [AlViolSlice1, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · change (Fin.append w (Fin.append y' u)) ∘ (iwIdx p n) ∈ AlDgListSlice p n f L
      rw [comp_iwIdx (p := p) (n := n) w (Fin.append y' u)]
      exact snoc_mem_AlDgListSlice.mpr ⟨hLW, hblk⟩
    · change (Fin.append w (Fin.append y' u)) ∘ (izIdx p n) ∈ AlDgListSlice p n f L
      rw [comp_izIdx (p := p) (n := n) w (Fin.append y' u),
        comp_zIdx_append (p := p) (n := n) w y' u]
      exact snoc_mem_AlDgListSlice.mpr ⟨hLZ, hlast⟩
    · change (Fin.append w (Fin.append y' u)) ∘ (icIdx p n) ∈ cmpSet
      rw [comp_icIdx (p := p) (n := n) w (Fin.append y' u)]
      rw [cmpSet, Set.mem_ofPred_eq, hblk, hlast]
      have h4 : 4 * (sliceDg f L w) ^ 2 < (sliceDg f L (zPt p n w y')) ^ 2 := by
        have habs : |2 * sliceDg f L w| < |sliceDg f L (zPt p n w y')| := by
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
          exact hineq
        have h2 := (sq_lt_sq (a := 2 * sliceDg f L w)
          (b := sliceDg f L (zPt p n w y'))).mpr habs
        rw [show (2 * sliceDg f L w) ^ 2 = 4 * (sliceDg f L w) ^ 2 by ring] at h2
        exact h2
      simpa using h4
    · change (Fin.append w (Fin.append y' u)) ∘ (cubeIdx p n) ∈ openCube n
      rw [comp_cubeIdx_append (p := p) (n := n) w y' u]
      exact hy'

/-- At a point `xPt l x y` the fibre violation set is described by the slice `u ↦ f l u`:
the `C^{|L|}`-smoothness at `pt x y` and the existence of `y' ∈ openCube n` with a strictly
larger `|∂^L|`. -/
theorem AlViolSlice_xPt_iff {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    xPt l x y ∈ AlViolSlice p n f L ↔
      ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u) (pt x y) ∧
      ∃ y' : Fin n → ℝ, y' ∈ openCube n ∧
        ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u) (pt x y') ∧
        2 * |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u) (pt x y)
              (fun j => Pi.single (L.get j) 1)| <
          |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u) (pt x y')
              (fun j => Pi.single (L.get j) 1)| := by
  rw [alphaViolSlice_iff]
  simp only [mem_SliceLocus_xPt, zPt_xPt, sliceDg, parPt_xPt, cubePt_xPt]

/-- **The fibre selection set, unfolded.**  `xPt l x y` lies in `AlZsetPureSlice p n f L` iff
`y` is a cube point, the slice `u ↦ f l u` is `C^{|L|}` at `pt x y`, and `xPt l x y` is not
beaten on the fibre.

This is the `AlDgListSlice`-version of `CurveFamAlpha_list_pure.mem_AlZsetPure_liftDir_iff`;
it turns membership in the selection set directly into the hypothesis/conclusion of
`CurveFamAlphaListPureSliced`. -/
theorem mem_AlZsetPureSlice_xPt_iff {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    xPt l x y ∈ AlZsetPureSlice p n f L ↔ y ∈ openCube n ∧
      ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u) (pt x y) ∧
      ∀ y' : Fin n → ℝ, y' ∈ openCube n →
        ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u) (pt x y') →
        |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u) (pt x y')
            (fun j => Pi.single (L.get j) 1)| ≤
          2 * |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u) (pt x y)
            (fun j => Pi.single (L.get j) 1)| := by
  have hy : (fun j : Fin n => xPt l x y (yIdx p n j)) = y := by
    funext j; rw [xPt_yIdx]
  rw [mem_AlZsetPureSlice, hy, Set.mem_compl_iff, mem_SliceLocus_xPt, AlViolSlice_xPt_iff]
  constructor
  · rintro ⟨hyc, hl, hnv⟩
    refine ⟨hyc, hl, ?_⟩
    intro y' hy' hl'
    by_contra hcon
    exact hnv ⟨hl, y', hy', hl', lt_of_not_ge hcon⟩
  · rintro ⟨hyc, hl, hmax⟩
    refine ⟨hyc, hl, ?_⟩
    rintro ⟨-, y', hy', hl', hlt⟩
    exact absurd (hmax y' hy' hl') (not_le.mpr hlt)

end SliceChoiceAux

open SliceChoiceAux

theorem CurveFamAlphaListPureSliced (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (hchoice : Work.WilkG4c.ChoiceHyp S) (p n : ℕ) :
    ∀ F0 : ℕ, ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (Λ : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        ∀ (L : List (Fin (n + 1))), L.length ≤ r →
          ∃ γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ),
            (∀ i : Fin n, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
                γ (fun k => w (Fin.castSucc k)) (w (Fin.last p)) i)
              ∈ S.Ω A (MvPolynomial.eval ![D, r] B) (p + 1 + 1)) ∧
            (∀ l ∈ Λ, ∀ x : ℝ,
              (∃ y : Fin n → ℝ, y ∈ WilkiesDesign.openCube n ∧
                ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                  (Work.WilkG4c.pt x y) ∧
                ∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
                  ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                    (Work.WilkG4c.pt x y') →
                  |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                    (Work.WilkG4c.pt x y') (fun j => Pi.single (L.get j) 1)| ≤
                    2 * |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                      (Work.WilkG4c.pt x y) (fun j => Pi.single (L.get j) 1)|) →
              γ l x ∈ WilkiesDesign.openCube n ∧
              ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                (Work.WilkG4c.pt x (γ l x)) ∧
              ∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
                ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                  (Work.WilkG4c.pt x y') →
                |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                  (Work.WilkG4c.pt x y') (fun j => Pi.single (L.get j) 1)| ≤
                  2 * |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
                    (Work.WilkG4c.pt x (γ l x)) (fun j => Pi.single (L.get j) 1)|) := by
  intro F0
  obtain ⟨a1, b1, hAlDg⟩ := AlDgListSliceMem S hcd hder p n F0
  obtain ⟨aC, bC, hC⟩ := hchoice (AlFzs p n a1) (p + 1) n
  refine ⟨AlA p n aC, AlB p n b1 bC, ?_⟩
  intro D r Λ f hΩ L hL
  have hPL : p + (n + 1) = (p + 1) + n := by omega
  have hgraph : graphOf (famFunHat f) ∈ S.Ω F0 D (p + (n + 1) + 1) := by
    rw [← famGraph_eq_graphOf_famFunHat]
    exact hΩ
  have hDg := hAlDg D f L hgraph
  have hZs := AlZsetPureSliceMem (L := L) hDg
  have hZs' := omega_ndrec hPL hZs
  obtain ⟨fsel, hsel, hGmem⟩ := hC
    (AlDzs p n (MvPolynomial.eval ![D, L.length] b1))
    (hPL ▸ AlZsetPureSlice p n f L) hZs'
  -- the degree inequality: this is the only place where `r` enters the picture
  have hβ : MvPolynomial.eval ![D, L.length] b1 ≤ MvPolynomial.eval ![D, r] b1 :=
    AlphaEvalMono b1 hL
  have hK1 : AlDzs p n (MvPolynomial.eval ![D, L.length] b1) ≤
      AlK1 p n + AlK2 * MvPolynomial.eval ![D, r] b1 := by
    dsimp only [AlDzs, AlDu, AlDalt, AlDviol, AlK1, AlK2]
    omega
  have hmono : bC.eval (AlDzs p n (MvPolynomial.eval ![D, L.length] b1)) ≤
      bC.eval (AlK1 p n + AlK2 * MvPolynomial.eval ![D, r] b1) :=
    Work.WilG1.Polynomial.eval_mono hK1
  have hdeg : bC.eval (AlDzs p n (MvPolynomial.eval ![D, L.length] b1)) +
      (32 * (((p + 1) + n) + (p + 1 + 1)) + 32) ≤
      MvPolynomial.eval ![D, r] (AlB p n b1 bC) := by
    rw [eval_AlB]
    have hK3 : 32 * (((p + 1) + n) + (p + 1 + 1)) + 32 ≤ AlK3 p n := by
      dsimp only [AlK3, AlK1]
      omega
    omega
  refine ⟨fun l x => fsel (Fin.snoc l x), ?_, ?_⟩
  · intro i
    have hmem := coordImage_mem (S := S)
      (ι := Fin.snoc (fun k : Fin (p + 1) => Fin.castAdd n k) (Fin.natAdd (p + 1) i)) hGmem
    have hge : graphOf (fun w : Fin (p + 1) → ℝ =>
          fsel (Fin.snoc (Fin.init w) (w (Fin.last p))) i) =
        coordImage (Fin.snoc (fun k : Fin (p + 1) => Fin.castAdd n k) (Fin.natAdd (p + 1) i))
          {z : Fin ((p + 1) + n) → ℝ | ∀ k : Fin n,
            z (Fin.natAdd (p + 1) k) = fsel (fun k' => z (Fin.castAdd n k')) k} :=
      CurveFam.graphOf_sel_eq_coordImage fsel i
    have hfun : (fun w : Fin (p + 1) → ℝ =>
          (fun l x => fsel (Fin.snoc l x)) (fun k => w (Fin.castSucc k)) (w (Fin.last p)) i)
        = (fun w : Fin (p + 1) → ℝ =>
          fsel (Fin.snoc (Fin.init w) (w (Fin.last p))) i) := rfl
    rw [hfun, hge]
    exact mem_mono hmem (AlA p n aC) (MvPolynomial.eval ![D, r] (AlB p n b1 bC)) le_rfl hdeg
  · intro l hl x hx
    obtain ⟨y, hyc, hyl, hmax⟩ := hx
    have hwit : Fin.append (Fin.snoc l x) y ∈ (hPL ▸ AlZsetPureSlice p n f L) := by
      rw [mem_ndrec, cast_snoc_append_xPt hPL]
      exact (mem_AlZsetPureSlice_xPt_iff f L l x y).mpr ⟨hyc, hyl, hmax⟩
    have hsel' := hsel (Fin.snoc l x) ⟨y, hwit⟩
    have hZs2 : xPt l x (fsel (Fin.snoc l x)) ∈ AlZsetPureSlice p n f L := by
      have h := (mem_ndrec hPL (AlZsetPureSlice p n f L)
        (Fin.append (Fin.snoc l x) (fsel (Fin.snoc l x)))).mp hsel'
      rwa [cast_snoc_append_xPt hPL] at h
    exact (mem_AlZsetPureSlice_xPt_iff f L l x (fsel (Fin.snoc l x))).mp hZs2

end Work.WilG4c
