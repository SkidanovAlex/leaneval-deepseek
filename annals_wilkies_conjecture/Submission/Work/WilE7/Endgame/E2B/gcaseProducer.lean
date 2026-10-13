import Mathlib
import Submission.Work.WilE7.Endgame.E2B.GSheets
import Submission.Work.WilE7.SheetData.gcase_cfs
import Submission.Work.WilE7.Endgame.Bv2.padSheets
import Submission.Work.WilE7.pad_stratum

set_option maxHeartbeats 1000000
noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

namespace Work.WilE7.Endgame.E2B

/-! ## The arithmetic of the `G`-case degree budget

The padded candidates `padStrat n (m+1) d (tidy (absSub S))` have degree
`≤ 2 * d + (1 + 2 * d) * S.X.deg` (`PadAux.padStrat_deg`), and `S.X.deg ≤ c.Dq.eval D`
(`CandSpec`).  The `G`-case may be called with any `d ≤ Fq`, so the budget `gcaseDeg` has to
dominate this uniformly; the next lemma is exactly that estimate. -/
private lemma gcaseDeg_ge {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    {D d Xd : ℕ} (hd : d ≤ Fq) (hX : Xd ≤ c.Dq.eval D) :
    2 * d + (1 + 2 * d) * Xd ≤ gcaseDeg c Fq Qq D := by
  unfold gcaseDeg
  have h1 : 2 * d ≤ 2 * Fq := by omega
  have h2 : 1 + 2 * d ≤ 1 + 2 * Fq := by omega
  have h3 : (1 + 2 * d) * Xd ≤ (1 + 2 * Fq) * c.Dq.eval D := Nat.mul_le_mul h2 hX
  have h4 : (1 + 2 * Fq) * c.Dq.eval D ≤ 2 * (1 + 2 * Fq) * (c.Dq.eval D + Qq.eval D) + 2 := by
    nlinarith [Nat.zero_le Fq, Nat.zero_le (c.Dq.eval D), Nat.zero_le (Qq.eval D)]
  omega

/-- **The `G`-case producer.**  The sheets `G.sc t j` of the active candidates over the base cell
`b`, together with their trichotomy (`hcls`), dichotomy (`hdich`) and bound (`hbnd`), produce the
level family `TT` and the decomposition `cfs b TT`.

The proof pads both the candidates and their sheets into the common frame `(n, d + m + 1)`
(`padSheets`), then applies the producer field `E2Pkg.hGcell` (the content of
`SheetData.gcase_cfs`) at `p₀ = n`, `mm = d + m`, `Zc = Z`, `Cc = b` and degree budget
`Dc = gcaseDeg c Fq Qq D`.  The last coordinate of the sheets is unchanged by the pinned middle
padding (`padSheets`), which transfers `hbnd`/`hcls`/`hdich` verbatim, and `c2.hBig`/`c2.hCB`
convert the padded format/degree bounds into the `c2.AB`/`c2.CB` bounds of the conclusion. -/
theorem gcaseProducer {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    {b : Set (Fin n → ℝ)} (G : GSheets c c2 P b)
    (hbnd : ∀ t j x, x ∈ b → |(G.sc t j x) (Fin.last m)| ≤ 1)
    (hcls : ∀ t j, (∀ x ∈ b, (G.sc t j x) (Fin.last m) = 1) ∨
      (∀ x ∈ b, (G.sc t j x) (Fin.last m) = -1) ∨
      (∀ x ∈ b, |(G.sc t j x) (Fin.last m)| < 1))
    (hdich : ∀ t t' j j', (∃ x ∈ b, (G.sc t j x) (Fin.last m) = (G.sc t' j' x) (Fin.last m)) →
      ∀ x ∈ b, (G.sc t j x) (Fin.last m) = (G.sc t' j' x) (Fin.last m))
    (d : ℕ) (hd : d ≤ Fq)
    (Z : WilkiesDesign.E.SemiPf (n + (d + m + 1))) (u : Fin (n + (d + m + 1)) → ℝ)
    (hu : u ∈ Z.set)
    (hC : b = WilkiesDesign.E.projFirst n (d + m + 1) '' connectedComponentIn Z.set u)
    (hCpf : WilkiesDesign.E.SubPf n b) (hCellc : WilkiesDesign.IsCell n b)
    (hZF : Z.fmt ≤ c2.Fbig) (hZD : Z.deg ≤ gcaseDeg c Fq Qq D) :
    ∃ (Kc : ℕ) (TT : Fin Kc → (Fin n → ℝ) → ℝ),
      (∀ i : Fin Kc, ContinuousOn (TT i) b) ∧
      (∀ x ∈ b, StrictMono fun i : Fin Kc => TT i x) ∧
      (∀ x ∈ b, ∀ i : Fin Kc, |TT i x| < 1) ∧
      (∀ t j, (∃ i : Fin Kc, ∀ x ∈ b, TT i x = (G.sc t j x) (Fin.last m)) ∨
        (∀ x ∈ b, (G.sc t j x) (Fin.last m) = 1) ∨
        (∀ x ∈ b, (G.sc t j x) (Fin.last m) = -1)) ∧
      (∀ i : Fin Kc, ∃ t j, ∀ x ∈ b, TT i x = (G.sc t j x) (Fin.last m)) ∧
      Kc ≤ (∑ t, G.kc t) ∧
      (∀ κ ∈ Work.WilE7.cfs b TT, Fin.init '' κ = b) ∧
      WilkiesDesign.E.IsCylDecompOn (n + 1) (Work.WilE7.cyl b) (Work.WilE7.cfs b TT) ∧
      (Work.WilE7.cfs b TT).card ≤ 2 * (∑ t, G.kc t) + 3 ∧
      (∀ κ ∈ Work.WilE7.cfs b TT, (∃ Pc : WilkiesDesign.E.StarPiece (n + 1),
          Pc.set = κ ∧ Pc.X.fmt ≤ c2.AB ∧ Pc.X.deg ≤ c2.CB.eval D) ∧
        WilkiesDesign.E.SubPf (n + 1) κ) := by
  classical
  -- the active candidates and their sheets, padded into the common frame `(n, d + m + 1)`
  let Xc : Fin G.r → WilkiesDesign.E.SemiPf (n + (d + m + 1)) := fun t =>
    Work.WilE7.padStrat n (m + 1) d (Work.WilE7.tidy (Work.CoreStep.absSub (G.S t)))
  let sc : (t : Fin G.r) → Fin (G.kc t) → (Fin n → ℝ) → (Fin (d + m + 1) → ℝ) :=
    fun t j x => Work.WilE7.padSection (m + 1) d (G.sc t j x)
  -- the padding transfers the sheet data, keeping the last (level) coordinate
  have hpad : ∀ t : Fin G.r,
      (∀ (j : Fin (G.kc t)) (x : Fin n → ℝ), x ∈ b → Fin.append x (sc t j x) ∈ (Xc t).set) ∧
      (∀ z ∈ (Xc t).set, WilkiesDesign.E.projFirst n (d + m + 1) z ∈ b →
        ∃ j : Fin (G.kc t), sc t j (WilkiesDesign.E.projFirst n (d + m + 1) z) =
          WilkiesDesign.E.projSnd n (d + m + 1) z) ∧
      (∀ (j : Fin (G.kc t)) (x : Fin n → ℝ), x ∈ b →
        (sc t j x) (Fin.last (d + m)) = (G.sc t j x) (Fin.last m)) ∧
      (∀ x ∈ b, Function.Injective fun j : Fin (G.kc t) => sc t j x) ∧
      (∀ j : Fin (G.kc t), ContinuousOn (sc t j) b) ∧
      ((Xc t).fmt = (G.S t).X.fmt + d) :=
    fun t => Work.WilE7.Endgame.Bv2.padSheets (d := d) (G.S t) b (G.kc t) (G.sc t)
      (G.hcont t) (G.hinj t) (G.hsub t) (G.hcov t)
  -- the padded candidates satisfy the format/degree budget of the producer
  have hSfmt : ∀ t : Fin G.r, (Xc t).fmt ≤ c2.Fbig := by
    intro t
    rw [(hpad t).2.2.2.2.2, c2.hBig]
    have h := G.hSfmt t
    omega
  have hSdeg : ∀ t : Fin G.r, (Xc t).deg ≤ gcaseDeg c Fq Qq D := by
    intro t
    have hXdeg : (G.S t).X.deg ≤ c.Dq.eval D :=
      le_trans (Work.WilE7.Endgame.E2B.stratum_Xdeg_le_deg (G.S t)) (G.hSdeg t)
    have h1 : (Xc t).deg
        ≤ (Work.WilE7.tidy (Work.CoreStep.absSub (G.S t))).deg
          + 2 * d * (Work.WilE7.tidy (Work.CoreStep.absSub (G.S t))).basics.length :=
      Work.WilE7.PadAux.padStrat_deg n (m + 1) d (Work.WilE7.tidy (Work.CoreStep.absSub (G.S t)))
    obtain ⟨h2a, h2b⟩ :=
      Work.WilE7.PadAux.tidy_bounds (n + (m + 1)) (Work.CoreStep.absSub (G.S t))
    have h2a' : (Work.WilE7.tidy (Work.CoreStep.absSub (G.S t))).deg ≤ c.Dq.eval D := by
      rw [Work.CoreStep.absSub_deg] at h2a; exact le_trans h2a hXdeg
    have h2b' : (Work.WilE7.tidy (Work.CoreStep.absSub (G.S t))).basics.length
        ≤ 1 + c.Dq.eval D := by
      rw [Work.CoreStep.absSub_deg] at h2b; exact le_trans h2b (Nat.add_le_add_left hXdeg 1)
    have h2 : (Work.WilE7.tidy (Work.CoreStep.absSub (G.S t))).deg
        + 2 * d * (Work.WilE7.tidy (Work.CoreStep.absSub (G.S t))).basics.length
        ≤ 2 * d + (1 + 2 * d) * c.Dq.eval D := by
      have hmul : 2 * d * (Work.WilE7.tidy (Work.CoreStep.absSub (G.S t))).basics.length
          ≤ 2 * d * (1 + c.Dq.eval D) := Nat.mul_le_mul_left (2 * d) h2b'
      have hsum := Nat.add_le_add h2a' hmul
      have heq : c.Dq.eval D + 2 * d * (1 + c.Dq.eval D)
          = 2 * d + (1 + 2 * d) * c.Dq.eval D := by ring
      rwa [heq] at hsum
    exact le_trans h1 (le_trans h2 (gcaseDeg_ge c hd (le_rfl)))
  -- the producer
  obtain ⟨Kc, TT, hTTcont, hTTmono, hTTbnd, hTcov, hTwit, hKle, hinit, hdec, hcard, hcell⟩ :=
    P.hGcell n (d + m) G.r Xc Z u hu b hC hCpf hCellc G.kc G.hkpos sc
      (fun t j => (hpad t).2.2.2.2.1 j)
      (fun t x hx => (hpad t).2.2.2.1 x hx)
      (fun t j x hx => (hpad t).1 j x hx)
      (fun t z hz hx => (hpad t).2.1 z hz hx)
      (fun t j x hx => by rw [(hpad t).2.2.1 j x hx]; exact hbnd t j x hx)
      (fun t j => by
        rcases hcls t j with h1 | h1 | h1
        · left; intro x hx; rw [(hpad t).2.2.1 j x hx]; exact h1 x hx
        · right; left; intro x hx; rw [(hpad t).2.2.1 j x hx]; exact h1 x hx
        · right; right; intro x hx; rw [(hpad t).2.2.1 j x hx]; exact h1 x hx)
      (fun t t' j j' hex => by
        have hex' : ∃ x ∈ b, (G.sc t j x) (Fin.last m) = (G.sc t' j' x) (Fin.last m) := by
          obtain ⟨x, hx, h⟩ := hex
          exact ⟨x, hx, by rw [← (hpad t).2.2.1 j x hx, ← (hpad t').2.2.1 j' x hx]; exact h⟩
        intro x hx
        rw [(hpad t).2.2.1 j x hx, (hpad t').2.2.1 j' x hx]
        exact hdich t t' j j' hex' x hx)
      (gcaseDeg c Fq Qq D)
      (fun t => ⟨hSfmt t, hSdeg t⟩)
      hZF hZD
  refine ⟨Kc, TT, hTTcont, hTTmono, hTTbnd, ?_, ?_, hKle, hinit, hdec, hcard, ?_⟩
  · -- every sheet level is either used or constant `±1`
    intro t j
    rcases hTcov t j with ⟨i, hi⟩ | h1 | h1
    · left; exact ⟨i, fun x hx => by rw [hi x hx, (hpad t).2.2.1 j x hx]⟩
    · right; left; intro x hx; rw [← (hpad t).2.2.1 j x hx]; exact h1 x hx
    · right; right; intro x hx; rw [← (hpad t).2.2.1 j x hx]; exact h1 x hx
  · -- every used level is the level of an actual sheet
    intro i
    obtain ⟨t, j, hw⟩ := hTwit i
    exact ⟨t, j, fun x hx => by rw [hw x hx, (hpad t).2.2.1 j x hx]⟩
  · -- the presentations of the cells of `cfs b TT`
    intro κ hκ
    obtain ⟨⟨Pc, hPset, hPfmt, hPdeg⟩, hsub⟩ := hcell κ hκ
    exact ⟨⟨Pc, hPset, le_trans hPfmt (by rw [c2.hAB]; exact le_max_left _ _),
      le_trans hPdeg (c2.hCB D)⟩, hsub⟩

end Work.WilE7.Endgame.E2B
