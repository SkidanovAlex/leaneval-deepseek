/-
  WilE5 — the flat leaf of a state is a `Good` stratum, with a *profile* test-order bound.

  This is the version of `Work.WilE5.Strat.flatLeaf_good` in which the order bound of the test
  list is the profile value `Ml (σ.B.length)` rather than a constant `Mtest`; since
  `flatStratumP X Ml NΦ σ` is *by definition* `flatStratum X (Ml σ.B.length) NΦ σ`, the proof is
  the constant-bound one at `Mtest := Ml σ.B.length`.

  The mathematical content is the Gabrielov–Vorobjov flatness argument in its fibrewise form:
  * `Good (a)` — the state's equations vanish on the flat leaf (they are among its conditions);
  * `Good (b)` — the fibre Jacobian of the pivots has full rank (`hdet` +
    `rank_eq_of_det_ne_zero_submatrix`);
  * `Good (c)` — fibrewise local equality: a point `w` with the same base as `z ∈ F_σ` and
    `H (w) = 0` for the pivots `H = hFun σ.B` lies in the flat leaf.  This is where `E3`
    (Gabrielov's multiplicity bound, in the frozen fibrewise form `hE3`) enters: applied to the
    *extended* system `extH (hFun σ.B) z = (H, x_i - z_i)` it shows that every flatness source
    `ψ ∈ σ.Φ` vanishes on the fibre level set `{H = 0}` near `z`; the conormal form
    (`fibre_conormal`) then propagates this to all iterated fibrewise operators `yOpSt m ψ`
    (induction on the order `mSum m`), and finally `hcube` keeps the fibre inside the cube and
    `continuity` keeps the state's strict conditions.
-/
import Mathlib
import Submission.Work.WilE5.SysL
import Submission.Work.WilE5.Profile
import Submission.Work.WilE5.Basic
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE5.Calc.fderiv_eq_sum_of_vanishes_on_levelSet
import Submission.Work.WilE5.Operators.rank_eq_of_det_ne_zero_submatrix
import Submission.Work.WilE5.Operators.detOp_extH_eq_zero
import Submission.Work.WilE5.Strat.auxiliary.flatSemiPf_set_eq
import Submission.Work.Strat.det_extJac_ne_zero
import Submission.Work.Strat.detOp_extH_eq
import Submission.Work.Strat.yOpSt_step
import Submission.Work.Strat.detOpSt_eq_zero_of_row_combination
import Submission.Work.WilE5.Strat.flatFoldReindex
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE5.Strat.flatFibreConormal

noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-! ## §1. Tools -/

/-- `eaEval c Q` is continuous in the point. -/
theorem flgp_continuous_eaEval {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    Continuous fun z : Fin k → ℝ => eaEval c Q z :=
  continuous_iff_continuousAt.mpr fun x =>
    (Work.WilE5.Calc.hasFDerivAt_eaEval c Q x).continuousAt

/-- The iterated fibrewise operator at the zero multi-index is the identity. -/
theorem flgp_yOpSt_zero_multi {p q r : ℕ} (c : EAChain (p + q) r)
    (B : List (EAPoly (p + q) r × Fin q)) (ψ : EAPoly (p + q) r) :
    yOpSt c B 0 ψ = ψ := by
  suffices h : ∀ L : List (Fin q), L.foldr (fun l g => (detOpSt c B l)^[0] g) ψ = ψ from
    h (List.finRange q)
  intro L
  induction L with
  | nil => rfl
  | cons a as ih => simpa [Function.iterate_zero_apply] using ih

/-- The `i`-th source of the flatness family, for an in-range index. -/
theorem flgp_testPoly_getElem {p q r : ℕ} (σ : St p q r) {i : ℕ} (hi : i < σ.Φ.length) :
    testPoly σ i = σ.Φ[i] := by
  unfold Work.WilE5.testPoly
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

/-- A valid test's source lies in the flatness family. -/
theorem flgp_testPoly_mem {p q r : ℕ} (σ : St p q r) (t : Test q) (hi : t.i < σ.Φ.length) :
    testPoly σ t.i ∈ σ.Φ := by
  rw [flgp_testPoly_getElem σ hi]
  exact List.getElem_mem ..

/-- Conjunction of finitely many eventual statements indexed by a list. -/
theorem flgp_eventually_list {α ι : Type*} {l : Filter α} (L : List ι) (P : ι → α → Prop)
    (h : ∀ i ∈ L, ∀ᶠ x in l, P i x) : ∀ᶠ x in l, ∀ i ∈ L, P i x := by
  induction L with
  | nil => simp
  | cons a as ih =>
    have h1 : ∀ᶠ x in l, P a x := h a (by simp)
    have h2 : ∀ᶠ x in l, ∀ i ∈ as, P i x := ih (fun i hi => h i (by simp [hi]))
    filter_upwards [h1, h2] with x hx1 hx2 i hi
    rcases List.mem_cons.mp hi with rfl | hmem
    · exact hx1
    · exact hx2 i hmem

/-! ## §2. The flat leaf with a constant test-order bound -/

/-- `flatLeaf_good` with the constant order bound `Mtest` exposed as an explicit variable: this
is the mathematical core, proved below and then instantiated at the profile `Ml`. -/
theorem flgp_flatLeaf_goodM {p q : ℕ} (X : SemiPf (p + q)) (Me : Polynomial ℕ)
    (Mtest NΦ : ℕ) (σ : St p q X.r) (A : Basic (p + q) X.r)
    (hA : A ∈ X.basics)
    (hE3 : ∀ (j : ℕ) (h : Fin j → EAPoly (p + q) X.r) (ι : Fin j → Fin (p + q))
      (f : EAPoly (p + q) X.r) (x : Fin (p + q) → ℝ),
      (∀ a, eaEval X.c (h a) x = 0) →
      (Matrix.of fun a b => eaEval X.c (eaD X.c (ι b) (h a)) x).det ≠ 0 →
      (∀ m : Fin (p + q) → ℕ, (∀ a, m (ι a) = 0) →
        (∑ l, m l ≤ Me.eval (∑ a, atomDeg (h a) + atomDeg f)) →
        eaEval X.c (opMono X.c h ι m f) x = 0) →
      ∀ᶠ y in nhds x, (∀ a, eaEval X.c (h a) y = 0) → eaEval X.c f y = 0)
    (hNΦ : σ.Φ.length ≤ NΦ)
    (hMu : ∀ ψ ∈ σ.Φ,
      Me.eval ((∑ a : Fin σ.B.length, atomDeg (hFun σ.B a)) + (2 * p) + atomDeg ψ) ≤ Mtest)
    (hcube : ∀ l : Fin q,
      intPoly (p := p) (r := X.r) l ∈ σ.ν ∨
        ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ facePoly (p := p) (r := X.r) l c ∈ σ.B.map Prod.fst)
    (hAΞ : ∀ f ∈ A.eqs, f ∈ (stCond σ).eqs)
    (hAν : ∀ g ∈ A.pos, g ∈ (stCond σ).pos)
    (hAΦ : ∀ f ∈ A.eqs, f ∈ σ.Φ)
    (hΞΦ : ∀ ψ ∈ σ.Ξ, ψ ∈ σ.Φ)
    (hΦΞ : ∀ ψ ∈ σ.Φ, ψ ∈ σ.Ξ)
    (hdet : ∀ z ∈ (stSemiPf X σ).set,
      (Matrix.of fun (a : Fin σ.B.length) (b : Fin σ.B.length) =>
        eaEval X.c (eaD X.c (pivFun σ.B b) (hFun σ.B a)) z).det ≠ 0) :
    (flatStratum X Mtest NΦ σ).Good := by
  classical
  intro z hz
  have hz' : z ∈ (flatSemiPf X Mtest NΦ σ).set := hz
  rw [Work.WilE5.Strat.aux.flatSemiPf_set_eq X Mtest NΦ σ] at hz'
  obtain ⟨hzX, hzst, hzflat⟩ := hz'
  have hzsemi : z ∈ (stSemiPf X σ).set := by
    show z ∈ (semiPfAnd X (stCond σ)).set
    rw [semiPfAnd_set]
    exact ⟨hzX, hzst⟩
  have hH : ∀ a : Fin σ.B.length, eaEval X.c (hFun σ.B a) z = 0 := fun a =>
    hzst.1 _ (List.mem_append_left _ (List.mem_map_of_mem (f := Prod.fst) (List.get_mem σ.B a)))
  refine ⟨hH, ?_, ?_⟩
  · -- `Good (b)`: the fibre Jacobian of the pivots has rank `σ.B.length`.
    have hdetz : (Matrix.of fun (a : Fin σ.B.length) (b : Fin σ.B.length) =>
        eaEval X.c (eaD X.c (pivFun σ.B b) (hFun σ.B a)) z).det ≠ 0 :=
      hdet z hzsemi
    have hsub : (Matrix.of fun (a : Fin σ.B.length) (l : Fin q) =>
        eaEval X.c (eaD X.c (yDir p l) (hFun σ.B a)) z).submatrix id
        (fun b => (σ.B.get b).2) =
        Matrix.of fun (a : Fin σ.B.length) (b : Fin σ.B.length) =>
          eaEval X.c (eaD X.c (pivFun σ.B b) (hFun σ.B a)) z := rfl
    exact Work.WilE5.Operators.rank_eq_of_det_ne_zero_submatrix
      (Matrix.of fun (a : Fin σ.B.length) (l : Fin q) =>
        eaEval X.c (eaD X.c (yDir p l) (hFun σ.B a)) z)
      (fun b => (σ.B.get b).2) (by rw [hsub]; exact hdetz)
  · -- `Good (c)`: fibrewise local equality.
    let pivdet : (Fin (p + q) → ℝ) → ℝ := fun w =>
      (Matrix.of fun a b => eaEval X.c (eaD X.c (pivFun σ.B b) (hFun σ.B a)) w).det
    have hzU : pivdet z ≠ 0 := hdet z hzsemi
    have hcont : Continuous pivdet := by
      refine Continuous.matrix_det ?_
      apply continuous_pi; intro a
      apply continuous_pi; intro b
      exact flgp_continuous_eaEval X.c _
    have hUo : IsOpen {w : Fin (p + q) → ℝ | pivdet w ≠ 0} := isOpen_ne.preimage hcont
    -- Every valid test's operator vanishes at `z` (this is the flat leaf's own condition).
    have hleaf_op : ∀ (m : Fin q → ℕ), (∀ a : Fin σ.B.length, m ((σ.B.get a).2) = 0) →
        mSum m ≤ Mtest → ∀ ψ ∈ σ.Φ, eaEval X.c (yOpSt X.c σ.B m ψ) z = 0 := by
      intro m hmv hmSum ψ hψ
      rcases eq_or_ne m 0 with hm0 | hm0
      · rw [hm0, flgp_yOpSt_zero_multi]
        exact hzst.1 ψ (List.mem_append_right _ (hΦΞ ψ hψ))
      · obtain ⟨l0, hl0⟩ := Function.ne_iff.mp hm0
        set l : Fin q := firstDir m ⟨l0, hl0⟩ with hldef
        have hlm : m l ≠ 0 := by rw [hldef]; exact firstDir_spec m ⟨l0, hl0⟩
        obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hψ
        set t : Test q := ⟨i, m, l⟩ with htdef
        have htL : t ∈ testL q Mtest NΦ := by
          unfold Work.WilE5.testL
          refine List.mem_filter.mpr ⟨?_, decide_eq_true hlm⟩
          refine List.mem_map.mpr ⟨(i, (m, l)), ?_, rfl⟩
          refine List.mem_product.mpr ⟨List.mem_range.mpr (by omega), ?_⟩
          refine List.mem_product.mpr ⟨Iff.mpr (Work.WilE5.mem_mList_iff m) (fun l' => ?_),
            List.mem_finRange l⟩
          exact le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l'))
            hmSum
        have hvalid : valid σ t := ⟨by simpa using hi, hmv⟩
        have hzf : eaEval X.c (opVal X.c σ t) z = 0 := by
          refine hzflat _ ?_
          simp only [Work.WilE5.flatEqs, List.mem_map]
          exact ⟨t, List.mem_filter.mpr ⟨htL, decide_eq_true hvalid⟩, rfl⟩
        have hop : opVal X.c σ t = yOpSt X.c σ.B m ψ := by
          show yOpSt X.c σ.B t.m (testPoly σ t.i) = yOpSt X.c σ.B m ψ
          have h1 : testPoly σ t.i = ψ := by
            rw [flgp_testPoly_getElem σ (by simpa using hi)]
            exact hget
          rw [show t.m = m from rfl, h1]
        rw [hop] at hzf
        exact hzf
    -- `E3` applied to the extended system: every source vanishes on the fibre level set.
    have hsource : ∀ ψ ∈ σ.Φ, ∀ᶠ y in 𝓝 z, projFirst p q y = projFirst p q z →
        (∀ a, eaEval X.c (hFun σ.B a) y = 0) → eaEval X.c ψ y = 0 := by
      intro ψ hψ
      refine (hE3 (σ.B.length + p) (extH (hFun σ.B) z) (extι (pivFun σ.B)) ψ z ?_ ?_ ?_).mono ?_
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          simpa only [extH, Fin.append_left] using hH b
        · intro j
          have hx : eaEval X.c (xShift (q := q) (r := X.r) z j) z = 0 := by
            rw [Work.WilE5.eaEval_xShift]; simp
          simpa only [extH, Fin.append_right] using hx
      · exact Work.Strat.det_extJac_ne_zero X.c (hFun σ.B) (pivFun σ.B)
          (fun a => ⟨(σ.B.get a).2, rfl⟩) z (hdet z hzsemi)
      · intro m hmv hbnd
        have hmbase : ∀ i : Fin p, m (Fin.castAdd q i) = 0 := by
          intro j
          have h := hmv (Fin.natAdd σ.B.length j)
          simpa only [extι, Fin.append_right] using h
        rw [opMono_extH_eq_yOpSt X.c σ.B z m ψ hmbase]
        refine hleaf_op (fun l => m (yDir p l)) ?_ ?_ ψ hψ
        · intro a
          have h := hmv (Fin.castAdd p a)
          simpa only [pivFun, extι, Fin.append_left] using h
        · have hsum : (∑ l : Fin (p + q), m l) = mSum (fun l : Fin q => m (yDir p l)) := by
            rw [Fin.sum_univ_add]
            simp only [Work.WilE5.mSum]
            rw [show (∑ i : Fin p, m (Fin.castAdd q i)) = 0 from
              Finset.sum_eq_zero fun i _ => hmbase i, zero_add]
            rfl
          rw [← hsum]
          refine le_trans hbnd ?_
          have hb : (∑ a : Fin (σ.B.length + p), atomDeg (extH (hFun σ.B) z a)) ≤
              (∑ a : Fin σ.B.length, atomDeg (hFun σ.B a)) + 2 * p :=
            sum_atomDeg_extH_le (hFun σ.B) z
          refine le_trans (Work.WilE5.eval_mono_nat ?_) (hMu ψ hψ)
          omega
      · intro y hy hbase hHy
        refine hy (fun a => Fin.addCases ?_ ?_ a)
        · intro b; simpa only [extH, Fin.append_left] using hHy b
        · intro j
          have hx : eaEval X.c (xShift (q := q) (r := X.r) z j) y = 0 := by
            rw [Work.WilE5.eaEval_xShift]
            exact sub_eq_zero.mpr (congrFun hbase j)
          simpa only [extH, Fin.append_right] using hx
    -- The multi-index induction: `yOpSt m ψ` vanishes on the fibre level set near `z`.
    have ind : ∀ (ψ : EAPoly (p + q) X.r), ψ ∈ σ.Φ →
        ∃ O : Set (Fin (p + q) → ℝ), IsOpen O ∧ z ∈ O ∧ (∀ w ∈ O, pivdet w ≠ 0) ∧
          ∀ (m : Fin q → ℕ), ∀ w ∈ O, projFirst p q w = projFirst p q z →
            (∀ a, eaEval X.c (hFun σ.B a) w = 0) →
            ∀ᶠ u in 𝓝 w, projFirst p q u = projFirst p q w →
              (∀ a, eaEval X.c (hFun σ.B a) u = 0) →
              eaEval X.c (yOpSt X.c σ.B m ψ) u = 0 := by
      intro ψ hψ
      obtain ⟨Oe, hOe, hOeo, hze⟩ := eventually_nhds_iff.mp (hsource ψ hψ)
      refine ⟨Oe ∩ {w | pivdet w ≠ 0}, hOeo.inter hUo, ⟨hze, hzU⟩, ?_, ?_⟩
      · intro w hw; exact hw.2
      · suffices H : ∀ n : ℕ, ∀ (m : Fin q → ℕ), mSum m = n →
            ∀ w ∈ Oe ∩ {w | pivdet w ≠ 0}, projFirst p q w = projFirst p q z →
              (∀ a, eaEval X.c (hFun σ.B a) w = 0) →
              ∀ᶠ u in 𝓝 w, projFirst p q u = projFirst p q w →
                (∀ a, eaEval X.c (hFun σ.B a) u = 0) →
                eaEval X.c (yOpSt X.c σ.B m ψ) u = 0 by
          intro m w hw hb hHw
          exact H (mSum m) m rfl w hw hb hHw
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro m hm w hw hb hHw
          rcases eq_or_ne m 0 with hm0 | hm0
          · subst hm0
            simp only [flgp_yOpSt_zero_multi]
            refine eventually_nhds_iff.mpr
              ⟨Oe ∩ {w | pivdet w ≠ 0}, ?_, hOeo.inter hUo, hw⟩
            intro u hu hub huH
            exact hOe u hu.1 (by rw [hub, hb]) huH
          · obtain ⟨l0, hl0⟩ := Function.ne_iff.mp hm0
            set l : Fin q := firstDir m ⟨l0, hl0⟩ with hldef
            have hlm : m l ≠ 0 := by rw [hldef]; exact firstDir_spec m ⟨l0, hl0⟩
            have hlmin : ∀ l' : Fin q, m l' ≠ 0 → l ≤ l' := by
              rw [hldef]; exact firstDir_min m ⟨l0, hl0⟩
            have hml : m l ≤ mSum m := by
              rw [Work.WilE5.mSum]
              exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
            have hlt : mSum (mDec m l) < n := by
              rw [← hm, Work.WilE5.mSum_mDec m l hlm]
              omega
            have hIH := ih (mSum (mDec m l)) hlt (mDec m l) rfl w hw hb hHw
            obtain ⟨Ow, hOw, hOwo, hwOw⟩ := eventually_nhds_iff.mp hIH
            refine eventually_nhds_iff.mpr
              ⟨(Oe ∩ {w | pivdet w ≠ 0}) ∩ Ow, ?_, (hOeo.inter hUo).inter hOwo, ⟨hw, hwOw⟩⟩
            intro u hu hub huH
            obtain ⟨huO, huOw⟩ := hu
            have hvu : ∀ᶠ v in 𝓝 u, projFirst p q v = projFirst p q u →
                (∀ a, eaEval X.c (hFun σ.B a) v = 0) →
                eaEval X.c (yOpSt X.c σ.B (mDec m l) ψ) v = 0 := by
              refine eventually_nhds_iff.mpr ⟨Ow, ?_, hOwo, huOw⟩
              intro v hv hvbase hvH
              exact hOw v hv (by rw [hvbase, hub, hb]) hvH
            have hvu' : ∀ᶠ v in 𝓝 u,
                (∀ i : Fin p, v (Fin.castAdd q i) = u (Fin.castAdd q i)) →
                (∀ a, eaEval X.c (hFun σ.B a) v = 0) →
                eaEval X.c (yOpSt X.c σ.B (mDec m l) ψ) v = 0 :=
              hvu.mono fun v hv hbase hH => hv (funext hbase) hH
            obtain ⟨lam, hlam⟩ := fibre_conormal X.c (hFun σ.B) (pivFun σ.B)
              (fun a => ⟨(σ.B.get a).2, rfl⟩) (yOpSt X.c σ.B (mDec m l) ψ) u huH huO.2 hvu'
            have hz0 := Work.Strat.detOpSt_eq_zero_of_row_combination X.c σ.B
              (yOpSt X.c σ.B (mDec m l) ψ) l u lam hlam
            rw [Work.Strat.yOpSt_step X.c σ.B m l hlm hlmin ψ]
            exact hz0
    -- The sources vanish on the fibre level set near `z`.
    have hsrcEv : ∀ᶠ w in 𝓝 z, projFirst p q w = projFirst p q z →
        (∀ a, eaEval X.c (hFun σ.B a) w = 0) → ∀ ψ ∈ σ.Φ, eaEval X.c ψ w = 0 := by
      refine (flgp_eventually_list σ.Φ (fun ψ w => projFirst p q w = projFirst p q z →
        (∀ a, eaEval X.c (hFun σ.B a) w = 0) → eaEval X.c ψ w = 0) ?_).mono ?_
      · intro ψ hψ
        obtain ⟨O, hOo, hzO, _, hO⟩ := ind ψ hψ
        refine eventually_nhds_iff.mpr ⟨O, ?_, hOo, hzO⟩
        intro w hw hb hHw
        have hthis := (hO 0 w hw hb hHw).self_of_nhds
        simp only [flgp_yOpSt_zero_multi] at hthis
        exact hthis trivial hHw
      · intro w hw hb hHw ψ hψ
        exact hw ψ hψ hb hHw
    -- The flat leaf's own equations vanish on the fibre level set near `z`.
    have hflatEv : ∀ᶠ w in 𝓝 z, projFirst p q w = projFirst p q z →
        (∀ a, eaEval X.c (hFun σ.B a) w = 0) →
        ∀ f ∈ flatEqs X.c Mtest NΦ σ, eaEval X.c f w = 0 := by
      have key : ∀ t ∈ testL q Mtest NΦ, ∀ᶠ w in 𝓝 z, projFirst p q w = projFirst p q z →
          (∀ a, eaEval X.c (hFun σ.B a) w = 0) → valid σ t →
          eaEval X.c (opVal X.c σ t) w = 0 := by
        intro t ht
        by_cases hv : valid σ t
        · obtain ⟨O, hOo, hzO, _, hO⟩ := ind (testPoly σ t.i) (flgp_testPoly_mem σ t hv.1)
          refine eventually_nhds_iff.mpr ⟨O, ?_, hOo, hzO⟩
          intro w hw hb hHw _
          have hthis := (hO t.m w hw hb hHw).self_of_nhds
          rw [show yOpSt X.c σ.B t.m (testPoly σ t.i) = opVal X.c σ t from rfl] at hthis
          exact hthis rfl hHw
        · exact Filter.Eventually.of_forall (fun w _ _ hval => absurd hval hv)
      refine (flgp_eventually_list (testL q Mtest NΦ) (fun t w => projFirst p q w = projFirst p q z →
        (∀ a, eaEval X.c (hFun σ.B a) w = 0) → valid σ t →
        eaEval X.c (opVal X.c σ t) w = 0) key).mono ?_
      intro w hw hb hHw f hf
      simp only [Work.WilE5.flatEqs, List.mem_map] at hf
      obtain ⟨t, ht, rfl⟩ := hf
      rw [List.mem_filter] at ht
      exact hw t ht.1 hb hHw (of_decide_eq_true ht.2)
    -- The strict positivity conditions of the state survive near `z`.
    have hνEv : ∀ᶠ w in 𝓝 z, ∀ g ∈ σ.ν, 0 < eaEval X.c g w := by
      refine flgp_eventually_list σ.ν (fun g w => 0 < eaEval X.c g w) ?_
      intro g hg
      exact (isOpen_lt continuous_const (flgp_continuous_eaEval X.c g)).mem_nhds (hzst.2 g hg)
    -- The fibre stays inside the cube.
    have hcubeEv : ∀ᶠ w in 𝓝 z, projFirst p q w = projFirst p q z →
        (∀ a, eaEval X.c (hFun σ.B a) w = 0) → ∀ l : Fin q, |w (yDir p l)| ≤ 1 := by
      have h1 : ∀ l : Fin q, ∀ᶠ w in 𝓝 z, projFirst p q w = projFirst p q z →
          (∀ a, eaEval X.c (hFun σ.B a) w = 0) → |w (yDir p l)| ≤ 1 := by
        intro l
        rcases hcube l with hν | ⟨cc, hcc, hface⟩
        · refine hνEv.mono ?_
          intro w hw hb hHw
          have hpos : 0 < eaEval X.c (intPoly (p := p) (r := X.r) l) w := hw _ hν
          rw [show intPoly (p := p) (r := X.r) l =
              MvPolynomial.C 1 - MvPolynomial.X (Sum.inl (yDir p l)) *
                MvPolynomial.X (Sum.inl (yDir p l)) from rfl, Work.WilE5.eaEval_intPoly] at hpos
          have h2 : (w (yDir p l)) ^ 2 < 1 := by linarith
          exact abs_le.mpr ⟨by nlinarith [sq_nonneg (w (yDir p l) + 1)],
            by nlinarith [sq_nonneg (w (yDir p l) - 1)]⟩
        · refine Filter.Eventually.of_forall ?_
          intro w hb hHw
          obtain ⟨b, hbB, hbf⟩ := List.mem_map.mp hface
          obtain ⟨b0, hb0⟩ := List.mem_iff_get.mp hbB
          have h0 : eaEval X.c (facePoly (p := p) (r := X.r) l cc) w = 0 := by
            have hthis := hHw b0
            rw [show hFun σ.B b0 = Prod.fst (σ.B.get b0) from rfl, hb0, hbf] at hthis
            exact hthis
          rw [show facePoly (p := p) (r := X.r) l cc =
              MvPolynomial.X (Sum.inl (yDir p l)) - MvPolynomial.C cc from rfl,
            Work.WilE5.eaEval_facePoly, sub_eq_zero] at h0
          rw [h0]
          rcases hcc with rfl | rfl <;> norm_num
      refine (Filter.eventually_all.mpr h1).mono ?_
      intro w hw hb hHw l
      exact hw l hb hHw
    -- Putting everything together.
    refine (hsrcEv.and (hflatEv.and (hνEv.and hcubeEv))).mono ?_
    rintro w ⟨hS, hF, hν, hC⟩ hb hHw
    have hHw' : ∀ a : Fin σ.B.length, eaEval X.c (hFun σ.B a) w = 0 := hHw
    show w ∈ (flatSemiPf X Mtest NΦ σ).set
    rw [Work.WilE5.Strat.aux.flatSemiPf_set_eq]
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, A, hA, ?_, ?_⟩
      · intro i
        rcases exists_castAdd_or_yDir i with ⟨j, rfl⟩ | ⟨l, rfl⟩
        · rw [show w (Fin.castAdd q j) = z (Fin.castAdd q j) from congrFun hb j]
          exact hzX.1 (Fin.castAdd q j)
        · exact hC hb hHw' l
      · intro f hf; exact hS hb hHw' f (hAΦ f hf)
      · intro g hg; exact hν g (hAν g hg)
    · refine ⟨?_, ?_⟩
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · obtain ⟨b, hbB, hbf⟩ := List.mem_map.mp hf
          obtain ⟨b0, hb0⟩ := List.mem_iff_get.mp hbB
          have hthis : eaEval X.c (hFun σ.B b0) w = 0 := hHw' b0
          rw [show hFun σ.B b0 = Prod.fst (σ.B.get b0) from rfl, hb0, hbf] at hthis
          exact hthis
        · exact hS hb hHw' f (hΞΦ f hf)
      · intro g hg; exact hν g hg
    · exact hF hb hHw'

/-! ## §3. The profile version -/

theorem flatLeafGoodP {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Me : Polynomial ℕ) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : Work.WilE5.St p q X.r) (A : WilkiesDesign.E.Basic (p + q) X.r)
    (hA : A ∈ X.basics)
    (hE3 : ∀ (j : ℕ) (h : Fin j → WilkiesDesign.E.EAPoly (p + q) X.r) (ι : Fin j → Fin (p + q))
      (f : WilkiesDesign.E.EAPoly (p + q) X.r) (x : Fin (p + q) → ℝ),
      (∀ a, WilkiesDesign.E.eaEval X.c (h a) x = 0) →
      (Matrix.of fun a b => WilkiesDesign.E.eaEval X.c (WilkiesDesign.E.eaD X.c (ι b) (h a)) x).det ≠ 0 →
      (∀ m : Fin (p + q) → ℕ, (∀ a, m (ι a) = 0) →
        (∑ l, m l ≤ Me.eval (∑ a, WilkiesDesign.E.atomDeg (h a) + WilkiesDesign.E.atomDeg f)) →
        WilkiesDesign.E.eaEval X.c (WilkiesDesign.E.opMono X.c h ι m f) x = 0) →
      ∀ᶠ y in nhds x, (∀ a, WilkiesDesign.E.eaEval X.c (h a) y = 0) →
        WilkiesDesign.E.eaEval X.c f y = 0)
    (hNΦ : σ.Φ.length ≤ NΦ)
    (hMu : ∀ ψ ∈ σ.Φ,
      Me.eval ((∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) + (2 * p) +
        WilkiesDesign.E.atomDeg ψ) ≤ Ml σ.B.length)
    (hcube : ∀ l : Fin q,
      Work.WilE5.intPoly (p := p) (r := X.r) l ∈ σ.ν ∨
        ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
          Work.WilE5.facePoly (p := p) (r := X.r) l c ∈ σ.B.map Prod.fst)
    (hAΞ : ∀ f ∈ A.eqs, f ∈ (Work.WilE5.stCond σ).eqs)
    (hAν : ∀ g ∈ A.pos, g ∈ (Work.WilE5.stCond σ).pos)
    (hAΦ : ∀ f ∈ A.eqs, f ∈ σ.Φ)
    (hΞΦ : ∀ ψ ∈ σ.Ξ, ψ ∈ σ.Φ)
    (hΦΞ : ∀ ψ ∈ σ.Φ, ψ ∈ σ.Ξ)
    (hdet : ∀ z ∈ (Work.WilE5.stSemiPf X σ).set,
      (Matrix.of fun (a : Fin σ.B.length) (b : Fin σ.B.length) =>
        WilkiesDesign.E.eaEval X.c (WilkiesDesign.E.eaD X.c (Work.WilE5.pivFun σ.B b)
          (Work.WilE5.hFun σ.B a)) z).det ≠ 0) :
    (Work.WilE5.flatStratumP X Ml NΦ σ).Good :=
  flgp_flatLeaf_goodM X Me (Ml σ.B.length) NΦ σ A hA hE3 hNΦ hMu hcube hAΞ hAν hAΦ hΞΦ hΦΞ hdet

end Work.WilE5.Strat
