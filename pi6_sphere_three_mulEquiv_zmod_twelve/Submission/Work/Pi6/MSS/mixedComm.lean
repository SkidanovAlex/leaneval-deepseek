import Mathlib
import Submission.Work.Pi6.MSS.e2Asm
import Submission.Work.Pi6.MSS.e2ColRho
import Submission.Work.Pi6.MSS.e2Row_exists
import Submission.Work.Pi6.MSS.e2Aux
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.mulEq
import Submission.Work.Pi6.MSS.mssMulCompat
import Submission.Work.Cohomology.cupZeroRight
import Submission.Work.Pi6.SQM.cup1CoboundaryR
import Submission.Work.Pi6.MSS.cup1MemCoFilt
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-!
# `Work.Pi6.MSS.mixedComm`: mixed graded commutativity on `E_2`

## What is proved here (the whole file is sorry-free)

* a toolbox of transports along equalities of degrees and their interaction with the Serre
  filtration (`mc_rec_*`, `mc_dPrev_eq`, `mc_serreCup_eq`, `mc_mkQ_smul`, …);
* `pdMulMixed_main` — **the mathematical core**: for `1 ≤ q, 1 ≤ s` and cycles
  `x ∈ Z_2^0(q)`, `y ∈ Z_2^s(s)` with `dy = 0`, the cup-1 coboundary formula
  (`Work.Pi6.SQM.cup1CoboundaryR`) plus the filtration estimate of the cup-1 faces
  (`Work.Pi6.MSS.cup1MemCoFilt`) show that
  `x ⌣ y - (-1)^{qs} y ⌣ x ∈ Z_1^{s+1} + B_2^s`, i.e. the two products have the same class in
  `E_2^{s,q}` with the Koszul sign;
* `pdMulMixed_q0`, `pdMulMixed_s0` — the degenerate cases (a `0`-cocycle is constant on the
  vertices of a simplex, `Work.Cohomology.cupZeroRight`);
* `pdMulMixed` — the honest-index statement
  `pCast (0+s = s+0) (q+s = s+q) (pd_mul 2 0 q s s (mkQ x) (mkQ y))
     = (-1)^{qs} • pd_mul 2 s s 0 q (mkQ y) (mkQ x)`.

## The assembly (the bidegree-indexed statement)

* `mc_pCast_inv_apply` / `mc_pCast_congr_apply` — the transport bookkeeping for `pCast`;
* `mc_d_eq_zero_of_pZ` — a `2`-cycle of the *bottom row* in degree `s` is a cocycle (its
  coboundary lies in `F^{s+2}C^{s+1} = 0`), which is what turns `pdMulMixed`'s `hymem` into its
  `hy`;
* `mc_pd_mul_comm` — the page-level (`pEraw`) form of the crux, obtained from `pdMulMixed` by
  `Submodule.mkQ_surjective` and `pCast_congr` (its casts are literally `Nat.add_comm`, which is
  the spelling that `mssMul_apply_pos` produces, so that `rw` can match it);
* `mc_mssMul_mixed` — **the bidegree-indexed statement**: `mssMul` of the column `E_2^{0,q}` and
  the bottom row `E_2^{s,0}` picks up the Koszul sign `(-1)^{s q}` upon reversal.  The proof
  transports both page elements to the honest indices `(0,q)` and `(s,s)` and back
  (`mc_pCast_inv_apply`), unfolds both products by `mssMul_apply_pos`, identifies the resulting
  `pd_mul` with the clean one by `pd_mul_pCast_apply`, applies `mc_pd_mul_comm`, and transports
  the answer back (`pCast_congr` + `pCast_comp_apply`);
* `mixedComm` — the requested lemma, immediate from `mc_mssMul_mixed` (`e2ColAll`, `e2Row` are
  the column resp. row maps).

Pitfalls (learned the hard way):
* `Cochain 𝕜 X n` (an `abbrev`) and `↑((serreCF 𝕜 E B p).C.X n)` are *definitionally* equal but
  `rw`/`simp` frequently fail to match across the two spellings, because unfolding
  `serreCF`/`SSetCochainComplex` is not allowed at `reducible` transparency.  *Always* write
  the terms of a statement with one consistent spelling, and connect the spellings with
  `mc_serreCup_eq` (`(𝕎).mul = cup`, an equation that `rw` accepts) and `serreCF_d_apply`
  (`(𝕎).d = cochainDiff`).
* `h ▸ x` as produced inside an *external* statement (e.g. `Cup1CobR`) cannot be rewritten by
  `rw` with a locally proved `(h ▸ x) = 0`; use `simp only [ … ]` (which handles the cast
  internally), or state the fact with the same elaboration.
* `omega` inside `show … by omega` in a statement and in a proof term are recognised as the same
  proof, but `by omega` and `Nat.add_comm …` are not; prefer naming the equalities.
* **`rw` cannot match `EI ((0 : ℤ), (q : ℤ))` against `EI_pair`'s `EI (↑0, ↑q)`** (the `OfNat`
  instance is not unfolded by the matcher).  Prove those equalities with
  `show EI ((0 : ℤ), (q : ℤ)) = 0 from EI_pair 0 q` instead.
* **The transparency setting matters.**  The `set_option backward.isDefEq.respectTransparency
  false` at the top of the file (needed by the cup-1 bookkeeping) makes `rw [pCast_comp_apply]`
  and `simp only [pCast_comp_apply]` *fail* to match a nested `pCast` whose index arguments are
  closed `EI`/`EN`-expressions (the `if` in `EI` has to be unfolded to unify the two indices).
  The assembly block below is therefore preceded by
  `set_option backward.isDefEq.respectTransparency true`.
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable

/-- `CohFilt.xcast` is the `Eq.rec` transport. -/
lemma mc_xcast_eq_rec {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {a b : ℕ} (h : a = b)
    (x : W.C.X a) : W.xcast h x = h ▸ x := by
  cases h; rfl

/-- A transport along a reflexive equality of degrees is the identity, for any proof term. -/
lemma mc_xcast_self_refl {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {a : ℕ} {h : a = a}
    (x : W.C.X a) : W.xcast h x = x := by
  rw [Subsingleton.elim h rfl, CohFilt.xcast_rfl]
  rfl

/-- Two consecutive transports along equalities of degrees. -/
lemma mc_xcast_xcast {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {a b c : ℕ} (h : a = b)
    (h' : b = c) (x : W.C.X a) : W.xcast h' (W.xcast h x) = W.xcast (h.trans h') x := by
  rw [← LinearMap.comp_apply, CohFilt.xcast_trans]

/-- The `Eq.rec` form of `xcast`. -/
lemma mc_rec_xcast {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {a b : ℕ} (h : a = b)
    (x : W.C.X a) : (h ▸ x) = W.xcast h x := (mc_xcast_eq_rec h x).symm

/-- The cup-1 product of anything with `0` on the right vanishes. -/
lemma mc_cup1_zero_right (𝕜 : Type) [CommRing 𝕜] (X : SSet.{0}) (n m : ℕ)
    (α : Work.Cohomology.Cochain 𝕜 X n) :
    Work.Cohomology.cup1 𝕜 X n m α 0 = 0 := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_cup1]
  refine Finset.sum_eq_zero fun s _ => ?_
  simp [Work.Cohomology.genEval]

/-- Transport of the differential of a `▸`-transported element. -/
lemma mc_rec_dW {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {a b : ℕ} (h : a = b)
    (h' : a + 1 = b + 1) (x : W.C.X a) :
    W.d b ((h ▸ x) : W.C.X b) = (h' ▸ (W.d a x) : W.C.X (b + 1)) := by
  cases h; cases h'; rfl

/-- The class of a scalar multiple of a cycle. -/
lemma mc_mkQ_smul {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {r a b : ℕ} (c : 𝕜)
    (z : ↥(pZ 𝕜 W r a b)) :
    Submodule.mkQ ((pDen 𝕜 W r a b).comap (pZ 𝕜 W r a b).subtype) (c • z)
      = c • Submodule.mkQ ((pDen 𝕜 W r a b).comap (pZ 𝕜 W r a b).subtype) z :=
  map_smul _ _ _

variable (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B))

local notation "𝕎" => serreCF 𝕜 E B p

/-! ## Toolbox: transports along equalities of degrees, and the concrete product -/

/-- The differential of a `2`-cycle of the zeroth column in degree `0` vanishes. -/
lemma mc_cochainDiff_of_pZ_deg0 (y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) 0)
    (hy : (y : (𝕎).C.X 0) ∈ pZ 𝕜 𝕎 2 0 0) :
    Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) y = 0 := by
  have h2 : (𝕎).d 0 y ∈ (𝕎).F (0 + 2) (0 + 1) :=
    Submodule.mem_comap.mp (Submodule.mem_inf.mp hy).2
  rw [show (0 + 2 : ℕ) = 1 + 1 from rfl, (𝕎).F_top 1, Submodule.mem_bot] at h2
  rw [← serreCF_d_apply 𝕜 E B p 0 y]
  exact h2

/-- The product of the Serre filtration is the Alexander–Whitney product. -/
lemma mc_serreCup_eq {n m : ℕ} (a : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n)
    (b : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) m) :
    (𝕎).mul n m a b = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) a b := by
  show serreCup 𝕜 p n m a b = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) a b
  rw [serreCup_apply]

/-- A transport along an equality of degrees respects the filtration. -/
lemma mc_rec_mem {t a b : ℕ} (h : a = b)
    (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) a) (hx : x ∈ (𝕎).F t a) :
    ((h ▸ x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) b) ∈ (𝕎).F t b) := by
  cases h; exact hx

/-- A transport along an equality of degrees respects the filtration (`W`-spelling). -/
lemma mc_rec_mem' {t a b : ℕ} (h : a = b) (x : (𝕎).C.X a) (hx : x ∈ (𝕎).F t a) :
    ((h ▸ x : (𝕎).C.X b) ∈ (𝕎).F t b) := by
  cases h; exact hx

/-- A transport along an equality of degrees preserves and reflects the filtration. -/
lemma mc_rec_mem_iff {t a b : ℕ} (h : a = b) (x : (𝕎).C.X a) :
    ((h ▸ x : (𝕎).C.X b) ∈ (𝕎).F t b) ↔ x ∈ (𝕎).F t a := by
  cases h; rfl

/-- The transport of degrees commutes with the coboundary. -/
lemma mc_rec_d {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1)
    (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) a) :
    (𝕎).d b (h ▸ x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) b)
      = (h' ▸ ((𝕎).d a x) : (𝕎).C.X (b + 1)) := by
  cases h; cases h'; rfl

lemma mc_rec_add {a b : ℕ} (h : a = b)
    (x y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) a) :
    ((h ▸ (x + y) : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) b)) = (h ▸ x) + (h ▸ y) := by
  cases h; rfl

lemma mc_rec_sub {a b : ℕ} (h : a = b)
    (x y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) a) :
    ((h ▸ (x - y) : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) b)) = (h ▸ x) - (h ▸ y) := by
  cases h; rfl

lemma mc_rec_smul {a b : ℕ} (h : a = b) (c : 𝕜)
    (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) a) :
    ((h ▸ (c • x) : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) b)) = c • (h ▸ x) := by
  cases h; rfl

lemma mc_rec_zero {a b : ℕ} (h : a = b) :
    ((h ▸ (0 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) a) :
        Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) b)) = 0 := by
  cases h; rfl

/-- `dPrev` as an iterated transport. -/
lemma mc_dPrev_eq {n : ℕ} (hn : 1 ≤ n)
    (v : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (n - 1)) :
    (𝕎).dPrev n v = (𝕎).xcast (show (n - 1) + 1 = n by omega) ((𝕎).d (n - 1) v) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [CohFilt.dPrev, CohFilt.d, CohFilt.xcast, CategoryTheory.eqToHom_refl,
    ModuleCat.hom_id]
  rfl

/-- `dPrev`, in `Eq.rec` form. -/
lemma mc_rec_dPrev {n : ℕ} (hn : 1 ≤ n)
    (v : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (n - 1)) :
    (𝕎).dPrev n v = ((show (n - 1) + 1 = n by omega) ▸ ((𝕎).d (n - 1) v) : (𝕎).C.X n) := by
  rw [mc_dPrev_eq 𝕜 E B p hn v]
  exact mc_xcast_eq_rec (show (n - 1) + 1 = n by omega) ((𝕎).d (n - 1) v)

/-! ## The mixed commutativity on the honest page indices -/

/-- **The main case** (`1 ≤ q`, `1 ≤ s`): the cup-1 coboundary formula. -/
lemma pdMulMixed_main (q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
    (y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) s)
    (hxmem : (x : (𝕎).C.X q) ∈ pZ 𝕜 𝕎 2 0 q)
    (hymem : (y : (𝕎).C.X s) ∈ pZ 𝕜 𝕎 2 s s)
    (hy : (𝕎).d s y = 0) :
    pCast 𝕜 𝕎 2 (by omega : 0 + s = s + 0) (by omega : q + s = s + q)
        (pd_mul 2 0 q s s
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 0 q).comap (pZ 𝕜 𝕎 2 0 q).subtype) ⟨x, hxmem⟩)
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 s s).comap (pZ 𝕜 𝕎 2 s s).subtype) ⟨y, hymem⟩))
      = (-1 : 𝕜) ^ (q * s) •
          pd_mul 2 s s 0 q
            (Submodule.mkQ ((pDen 𝕜 𝕎 2 s s).comap (pZ 𝕜 𝕎 2 s s).subtype) ⟨y, hymem⟩)
            (Submodule.mkQ ((pDen 𝕜 𝕎 2 0 q).comap (pZ 𝕜 𝕎 2 0 q).subtype) ⟨x, hxmem⟩) := by
  have hdy : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) y = 0 := by
    rw [← serreCF_d_apply 𝕜 E B p s y]; exact hy
  have hX0 : x ∈ (𝕎).F 0 q := (Submodule.mem_inf.mp hxmem).1
  have hY0 : y ∈ (𝕎).F s s := (Submodule.mem_inf.mp hymem).1
  have hX2 : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x ∈ (𝕎).F 2 (q + 1) := by
    have h : (𝕎).d q x ∈ (𝕎).F (0 + 2) (q + 1) :=
      Submodule.mem_comap.mp (Submodule.mem_inf.mp hxmem).2
    rw [serreCF_d_apply 𝕜 E B p q x] at h
    exact h
  have hX2d : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E)
      (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x) = 0 := by
    have hdx : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x = (𝕎).d q x :=
      (serreCF_d_apply 𝕜 E B p q x).symm
    rw [hdx, ← serreCF_d_apply 𝕜 E B p (q + 1) ((𝕎).d q x)]
    exact pd_d_comp_d_apply (𝕜 := 𝕜) (W := 𝕎) q (x : (𝕎).C.X q)
  set c1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (q + s - 1) :=
    Work.Cohomology.cup1 𝕜 (Work.SSS.sSing E) q s x y with hc1
  set w : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) ((q + 1) + s - 1) :=
    Work.Cohomology.cup1 𝕜 (Work.SSS.sSing E) (q + 1) s
      (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x) y with hw
  have hFc1 : c1 ∈ (𝕎).F (0 + s - 1) (q + s - 1) :=
    cup1MemCoFilt 𝕜 (Work.SSS.sSingP p) 0 s q s x y hX0 hY0
  have hFw : w ∈ (𝕎).F (2 + s - 1) ((q + 1) + s - 1) :=
    cup1MemCoFilt 𝕜 (Work.SSS.sSingP p) 2 s (q + 1) s
      (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x) y hX2 hY0
  have hcupMem : Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y ∈ (𝕎).F s (q + s) := by
    have h := (𝕎).mul_filt 0 s q s x y hX0 hY0
    rw [show (0 + s : ℕ) = s from by omega] at h
    rwa [mc_serreCup_eq 𝕜 E B p x y] at h
  have hyxMem : Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y x ∈ (𝕎).F s (s + q) := by
    have h := (𝕎).mul_filt s 0 s q y x hY0 hX0
    rw [show (s + 0 : ℕ) = s from by omega] at h
    rwa [mc_serreCup_eq 𝕜 E B p y x] at h
  have hNMem : ((-1 : 𝕜) ^ (q * s) •
      ((Nat.add_comm s q) ▸ Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y x)) ∈ (𝕎).F s (q + s) :=
    Submodule.smul_mem _ _
      (mc_rec_mem 𝕜 E B p (Nat.add_comm s q) (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y x)
        hyxMem)
  have hD0 : (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y
        - (-1 : 𝕜) ^ (q * s) •
            ((Nat.add_comm s q) ▸ Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y x) :
          Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (q + s))
      = ((show (q + s - 1) + 1 = q + s by omega) ▸
            (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) c1))
        + ((show (q + 1) + s - 1 = q + s by omega) ▸ w) := by
    have hform := Work.Pi6.SQM.cup1CoboundaryR 𝕜 (Work.SSS.sSing E) q s x y hq hs
    simp only [← hc1, ← hw, hdy, mc_cup1_zero_right, smul_zero, add_zero] at hform
    have h1 : (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y
          - (-1 : 𝕜) ^ (q * s) •
              ((Nat.add_comm s q) ▸ Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y x)
          - ((show (q + 1) + s - 1 = q + s by omega) ▸ w))
        = ((show (q + s - 1) + 1 = q + s by omega) ▸
            (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) c1)) := by
      simpa only [add_zero] using hform.symm
    have h2 : (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y
          - (-1 : 𝕜) ^ (q * s) •
              ((Nat.add_comm s q) ▸ Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y x))
        = ((Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y
              - (-1 : 𝕜) ^ (q * s) •
                  ((Nat.add_comm s q) ▸ Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y x)
              - ((show (q + 1) + s - 1 = q + s by omega) ▸ w))
            + ((show (q + 1) + s - 1 = q + s by omega) ▸ w)) := by
      abel
    exact h2.trans (congrArg (fun z => z + ((show (q + 1) + s - 1 = q + s by omega) ▸ w)) h1)
  have hwF' : w ∈ (𝕎).F (s + 1) ((q + 1) + s - 1) := by
    have h := hFw
    rw [show (2 + s - 1 : ℕ) = s + 1 from by omega] at h
    exact h
  have hTF : ((show (q + 1) + s - 1 = q + s by omega) ▸ w) ∈ (𝕎).F (s + 1) (q + s) :=
    mc_rec_mem 𝕜 E B p (show (q + 1) + s - 1 = q + s by omega) w hwF'
  have hUF : ((show (q + s - 1) + 1 = q + s by omega) ▸
        (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) c1)) ∈ (𝕎).F s (q + s) := by
    have h1 : ((show (q + s - 1) + 1 = q + s by omega) ▸
          (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) c1))
        = (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y
            - (-1 : 𝕜) ^ (q * s) •
                ((Nat.add_comm s q) ▸ Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y x))
          - ((show (q + 1) + s - 1 = q + s by omega) ▸ w) := by
      rw [hD0]; abel
    rw [h1]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hcupMem hNMem) ((𝕎).F_mono s (q + s) hTF)
  have hc1F : c1 ∈ (𝕎).F (s + 1 - 2) ((q + s) - 1) := by
    have h := pd_transport_mem' (𝕜 := 𝕜) (W := 𝕎) (t := 0 + s - 1) (t' := s + 1 - 2)
      (by omega) (by omega : q + s - 1 = (q + s) - 1) hFc1
    simpa using h
  have hU_pB : ((show (q + s - 1) + 1 = q + s by omega) ▸
        (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) c1)) ∈ pB 𝕜 𝕎 2 s (q + s) := by
    have hdPrev : (𝕎).dPrev (q + s) c1
        = ((show (q + s - 1) + 1 = q + s by omega) ▸
            (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) c1)) := by
      rw [mc_rec_dPrev 𝕜 E B p (by omega : 1 ≤ q + s) c1, serreCF_d_apply]
    rw [← hdPrev]
    refine ⟨?_, Submodule.mem_map_of_mem hc1F⟩
    rwa [hdPrev]
  have hT_pZ : ((show (q + 1) + s - 1 = q + s by omega) ▸ w) ∈ pZ 𝕜 𝕎 1 (s + 1) (q + s) := by
    refine ⟨hTF, ?_⟩
    refine Submodule.mem_comap.mpr ?_
    have hdT := mc_rec_dW (W := 𝕎) (a := (q + 1) + s - 1) (b := q + s)
      (show (q + 1) + s - 1 = q + s by omega)
      (show ((q + 1) + s - 1) + 1 = (q + s) + 1 by omega) w
    rw [hdT]
    have hdwF : (𝕎).d ((q + 1) + s - 1) w ∈ (𝕎).F (s + 2) (((q + 1) + s - 1) + 1) := by
      have hcocy := Work.Cohomology.cup1Identity 𝕜 (Work.SSS.sSing E) (q + 1) s
        (by omega : 1 ≤ q + 1) hs (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x) y
        hX2d hdy
      rw [← hw] at hcocy
      rw [← serreCF_d_apply 𝕜 E B p ((q + 1) + s - 1) w] at hcocy
      have hR : ((Work.Cohomology.cup 𝕜 (Work.SSS.sSing E)
            (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x) y
          - (-1 : 𝕜) ^ ((q + 1) * s) •
              ((Nat.add_comm s (q + 1)) ▸
                (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y
                  (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x))))
          ∈ (𝕎).F (2 + s) ((q + 1) + s)) := by
        refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)
        · have h := (𝕎).mul_filt 2 s (q + 1) s
            (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x) y hX2 hY0
          rwa [mc_serreCup_eq 𝕜 E B p (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x) y]
            at h
        · have hyx2 : (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y
              (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x)
              ∈ (𝕎).F (s + 2) (s + (q + 1))) := by
            have h := (𝕎).mul_filt s 2 s (q + 1) y
              (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x) hY0 hX2
            rwa [mc_serreCup_eq 𝕜 E B p y (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x)]
              at h
          have htrans := mc_rec_mem 𝕜 E B p (Nat.add_comm s (q + 1)) _ hyx2
          rwa [show (s + 2 : ℕ) = 2 + s from by omega] at htrans
      have h1 : ((show ((q + 1) + s - 1) + 1 = (q + 1) + s by omega) ▸
            ((𝕎).d ((q + 1) + s - 1) w)) ∈ (𝕎).F (2 + s) ((q + 1) + s) := by
        rw [hcocy]; exact hR
      have h2 := (mc_rec_mem_iff 𝕜 E B p (show ((q + 1) + s - 1) + 1 = (q + 1) + s by omega)
        ((𝕎).d ((q + 1) + s - 1) w)).mp h1
      rwa [show (2 + s : ℕ) = s + 2 from by omega] at h2
    have htrans := mc_rec_mem' 𝕜 E B p
      (show ((q + 1) + s - 1) + 1 = (q + s) + 1 by omega) ((𝕎).d ((q + 1) + s - 1) w) hdwF
    rwa [show (s + 2 : ℕ) = (s + 1) + 1 from by omega] at htrans
  have hmem : ((show (q + s - 1) + 1 = q + s by omega) ▸
        (Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) c1))
      + ((show (q + 1) + s - 1 = q + s by omega) ▸ w) ∈ pDen 𝕜 𝕎 2 s (q + s) :=
    Submodule.add_mem _ (Submodule.mem_sup_right hU_pB) (Submodule.mem_sup_left hT_pZ)
  rw [← hD0] at hmem
  have hmain : ((Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) x y
        - (-1 : 𝕜) ^ (q * s) •
            ((Nat.add_comm s q) ▸ Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y x) :
          Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (q + s))
      ∈ pDen 𝕜 𝕎 2 s (q + s)) := hmem
  -- rewrite the library product into the product of the filtered complex
  have hmain'' : ((𝕎).mul q s x y
        - (-1 : 𝕜) ^ (q * s) • ((𝕎).xcast (Nat.add_comm s q) ((𝕎).mul s q y x)) :
          (𝕎).C.X (q + s)) ∈ pDen 𝕜 𝕎 2 s (q + s) := by
    rw [← mc_serreCup_eq 𝕜 E B p x y] at hmain
    rw [← mc_serreCup_eq 𝕜 E B p y x] at hmain
    rw [mc_rec_xcast (Nat.add_comm s q) ((𝕎).mul s q y x)] at hmain
    exact hmain
  -- descend to the pages
  rw [pd_mul_nat, pd_mul_nat, ← pEcast_hom_apply, pd_pEcast_mkQ']
  rw [← mc_mkQ_smul]
  refine (pd_mkQ_eq_iff 2 (s + 0) (s + q) _ _).mpr ?_
  show (𝕎).xcast (show q + s = s + q by omega) ((𝕎).mul q s x y)
      - (-1 : 𝕜) ^ (q * s) • ((𝕎).mul s q y x : (𝕎).C.X (s + q))
      ∈ pDen 𝕜 𝕎 2 (s + 0) (s + q)
  have hsplit : (𝕎).xcast (show q + s = s + q by omega)
        ((𝕎).mul q s x y
          - (-1 : 𝕜) ^ (q * s) • ((𝕎).xcast (Nat.add_comm s q) ((𝕎).mul s q y x)))
      = (𝕎).xcast (show q + s = s + q by omega) ((𝕎).mul q s x y)
        - (-1 : 𝕜) ^ (q * s) • ((𝕎).mul s q y x : (𝕎).C.X (s + q)) := by
    rw [map_sub, map_smul]
    congr 1
    rw [mc_xcast_xcast, mc_xcast_self_refl]
  rw [← hsplit]
  exact (pd_xcast_mem_pDen_iff (𝕜 := 𝕜) (W := 𝕎) (r := 2) (s := s)
    (show q + s = s + q by omega) _).mpr hmain''


/-- The case `q = 0` of `pdMulMixed`. -/
lemma pdMulMixed_q0 (s : ℕ) (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) 0)
    (y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) s)
    (hxmem : (x : (𝕎).C.X 0) ∈ pZ 𝕜 𝕎 2 0 0)
    (hymem : (y : (𝕎).C.X s) ∈ pZ 𝕜 𝕎 2 s s)
    (_hy : (𝕎).d s y = 0) :
    pCast 𝕜 𝕎 2 (by omega : 0 + s = s + 0) (by omega : 0 + s = s + 0)
        (pd_mul 2 0 0 s s
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 0 0).comap (pZ 𝕜 𝕎 2 0 0).subtype) ⟨x, hxmem⟩)
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 s s).comap (pZ 𝕜 𝕎 2 s s).subtype) ⟨y, hymem⟩))
      = pd_mul 2 s s 0 0
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 s s).comap (pZ 𝕜 𝕎 2 s s).subtype) ⟨y, hymem⟩)
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 0 0).comap (pZ 𝕜 𝕎 2 0 0).subtype) ⟨x, hxmem⟩) := by
  have hx : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x = 0 :=
    mc_cochainDiff_of_pZ_deg0 𝕜 E B p x hxmem
  have hcast : ∀ (h : s + 0 = 0 + s),
      (𝕎).xcast h ((𝕎).mul s 0 y x) = (𝕎).mul 0 s x y := by
    intro h
    rw [Subsingleton.elim h (Nat.add_comm s 0), mc_xcast_eq_rec]
    show (Nat.add_comm s 0) ▸ (serreCup 𝕜 p s 0 y x) = serreCup 𝕜 p 0 s x y
    rw [serreCup_apply, serreCup_apply]
    exact Work.Cohomology.cupZeroRight 𝕜 (Work.SSS.sSing E) s y x hx
  rw [pd_mul_nat, pd_mul_nat, ← pEcast_hom_apply, pd_pEcast_mkQ']
  refine pd_mkQ_congr ?_
  show (𝕎).xcast _ (((pd_mulZ 2 0 0 s s) ⟨x, hxmem⟩) ⟨y, hymem⟩).1
    = (((pd_mulZ 2 s s 0 0) ⟨y, hymem⟩) ⟨x, hxmem⟩).1
  have hstep : (𝕎).mul 0 s x y = (𝕎).xcast (Nat.add_comm s 0) ((𝕎).mul s 0 y x) :=
    (hcast (Nat.add_comm s 0)).symm
  rw [pd_mulZ_val, pd_mulZ_val, hstep, mc_xcast_xcast, mc_xcast_self_refl]

/-- The case `s = 0` of `pdMulMixed`. -/
lemma pdMulMixed_s0 (q : ℕ) (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
    (y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) 0)
    (hxmem : (x : (𝕎).C.X q) ∈ pZ 𝕜 𝕎 2 0 q)
    (hymem : (y : (𝕎).C.X 0) ∈ pZ 𝕜 𝕎 2 0 0)
    (hy : (𝕎).d 0 y = 0) :
    pCast 𝕜 𝕎 2 (by omega : 0 + 0 = 0 + 0) (by omega : q + 0 = 0 + q)
        (pd_mul 2 0 q 0 0
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 0 q).comap (pZ 𝕜 𝕎 2 0 q).subtype) ⟨x, hxmem⟩)
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 0 0).comap (pZ 𝕜 𝕎 2 0 0).subtype) ⟨y, hymem⟩))
      = pd_mul 2 0 0 0 q
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 0 0).comap (pZ 𝕜 𝕎 2 0 0).subtype) ⟨y, hymem⟩)
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 0 q).comap (pZ 𝕜 𝕎 2 0 q).subtype) ⟨x, hxmem⟩) := by
  have hyc : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) y = 0 := by
    rw [← serreCF_d_apply 𝕜 E B p 0 y]; exact hy
  have hcup : ∀ (h : q + 0 = 0 + q),
      (𝕎).xcast h ((𝕎).mul q 0 x y) = (𝕎).mul 0 q y x := by
    intro h
    rw [Subsingleton.elim h (Nat.add_comm q 0), mc_xcast_eq_rec]
    show (Nat.add_comm q 0) ▸ (serreCup 𝕜 p q 0 x y) = serreCup 𝕜 p 0 q y x
    rw [serreCup_apply, serreCup_apply]
    exact Work.Cohomology.cupZeroRight 𝕜 (Work.SSS.sSing E) q x y hyc
  rw [pd_mul_nat, pd_mul_nat, ← pEcast_hom_apply, pd_pEcast_mkQ']
  refine pd_mkQ_congr ?_
  show (𝕎).xcast _ (((pd_mulZ 2 0 q 0 0) ⟨x, hxmem⟩) ⟨y, hymem⟩).1
    = (((pd_mulZ 2 0 0 0 q) ⟨y, hymem⟩) ⟨x, hxmem⟩).1
  have hstep : (𝕎).mul q 0 x y = (𝕎).xcast (Nat.add_comm q 0).symm ((𝕎).mul 0 q y x) := by
    rw [← hcup (Nat.add_comm q 0), mc_xcast_xcast, mc_xcast_self_refl]
  rw [pd_mulZ_val, pd_mulZ_val, hstep, mc_xcast_xcast, mc_xcast_self_refl]

/-- **The mixed commutativity on the honest page indices.** -/
theorem pdMulMixed (s q : ℕ) (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
    (y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) s)
    (hxmem : (x : (𝕎).C.X q) ∈ pZ 𝕜 𝕎 2 0 q)
    (hymem : (y : (𝕎).C.X s) ∈ pZ 𝕜 𝕎 2 s s)
    (hy : (𝕎).d s y = 0) :
    pCast 𝕜 𝕎 2 (by omega : 0 + s = s + 0) (by omega : q + s = s + q)
        (pd_mul 2 0 q s s
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 0 q).comap (pZ 𝕜 𝕎 2 0 q).subtype) ⟨x, hxmem⟩)
          (Submodule.mkQ ((pDen 𝕜 𝕎 2 s s).comap (pZ 𝕜 𝕎 2 s s).subtype) ⟨y, hymem⟩))
      = (-1 : 𝕜) ^ (q * s) •
          pd_mul 2 s s 0 q
            (Submodule.mkQ ((pDen 𝕜 𝕎 2 s s).comap (pZ 𝕜 𝕎 2 s s).subtype) ⟨y, hymem⟩)
            (Submodule.mkQ ((pDen 𝕜 𝕎 2 0 q).comap (pZ 𝕜 𝕎 2 0 q).subtype) ⟨x, hxmem⟩) := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    rw [show (-1 : 𝕜) ^ (q * 0) = 1 from by simp, one_smul]
    exact pdMulMixed_s0 𝕜 E B p q x y hxmem hymem hy
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [show (-1 : 𝕜) ^ (0 * s) = 1 from by simp, one_smul]
    exact pdMulMixed_q0 𝕜 E B p s x y hxmem hymem hy
  exact pdMulMixed_main 𝕜 E B p q s hq hs x y hxmem hymem hy


-- the assembly below matches `pCast` terms whose index arguments are closed `EI`/`EN`
-- expressions; that requires the older (transparency-respecting) `isDefEq`.
set_option backward.isDefEq.respectTransparency true

/-! ## Assembly: from the concrete page product to `mssMul` -/

/-- The transport `pCast` along the transposed index equalities is a left inverse of `pCast`. -/
lemma mc_pCast_inv_apply {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {r a b m k : ℕ}
    (h : a = b) (h' : m = k) (x : pEraw 𝕜 W r a m) :
    pCast 𝕜 W r h.symm h'.symm (pCast 𝕜 W r h h' x) = x := by
  rw [pCast_comp_apply 𝕜 W r h h.symm h' h'.symm x]
  rw [show h.trans h.symm = rfl from Subsingleton.elim _ _,
    show h'.trans h'.symm = rfl from Subsingleton.elim _ _]
  exact pCast_apply_self 𝕜 W r x

/-- Two transports of a page along equalities with the same endpoints agree. -/
lemma mc_pCast_congr_apply {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {r s s' n n' : ℕ}
    (h1 h2 : s = s') (h1' h2' : n = n') (x : pEraw 𝕜 W r s n) :
    pCast 𝕜 W r h1 h1' x = pCast 𝕜 W r h2 h2' x := by
  rw [pCast_congr 𝕜 W r h1 h2 h1' h2']

/-- A `2`-cycle of the bottom row of the `E_2` page is a cocycle. -/
lemma mc_d_eq_zero_of_pZ {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} (s : ℕ)
    (v : ↥(pZ 𝕜 W 2 s s)) : W.d s v.1 = 0 := by
  have h := v.2.2
  rw [show s + 2 = (s + 1) + 1 from rfl, W.F_top (s + 1)] at h
  simpa using h

/-- **Graded commutativity of the concrete page product** on the column and the bottom row. -/
lemma mc_pd_mul_comm (s q : ℕ) (x : pEraw 𝕜 𝕎 2 0 q) (y : pEraw 𝕜 𝕎 2 s s) :
    pCast 𝕜 𝕎 2 (Nat.add_comm 0 s) (Nat.add_comm q s) (pd_mul 2 0 q s s x y)
      = (-1 : 𝕜) ^ (q * s) • pd_mul 2 s s 0 q y x := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 𝕎 2 0 q).comap (pZ 𝕜 𝕎 2 0 q).subtype) x
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 𝕎 2 s s).comap (pZ 𝕜 𝕎 2 s s).subtype) y
  have hv : (𝕎).d s v.1 = 0 := mc_d_eq_zero_of_pZ s v
  refine (mc_pCast_congr_apply (W := 𝕎) (r := 2) (s := 0 + s) (s' := s + 0) (n := q + s)
    (n' := s + q) (Nat.add_comm 0 s) (show 0 + s = s + 0 by omega)
    (Nat.add_comm q s) (show q + s = s + q by omega)
    (pd_mul 2 0 q s s (Submodule.mkQ _ u) (Submodule.mkQ _ v))).trans ?_
  exact pdMulMixed 𝕜 E B p s q u.1 v.1 u.2 v.2 hv

/-- **Mixed graded commutativity in the bidegree-indexed pages**: the product of the column
`E_2^{0,q}` and the bottom row `E_2^{s,0}` picks up the Koszul sign `(-1)^{s q}` upon reversal. -/
theorem mc_mssMul_mixed (s q : ℕ)
    (h1 : ((0 : ℤ), (q : ℤ)) + ((s : ℤ), (0 : ℤ)) = ((s : ℤ), (q : ℤ)))
    (h2 : ((s : ℤ), (0 : ℤ)) + ((0 : ℤ), (q : ℤ)) = ((s : ℤ), (q : ℤ)))
    (x : mssE 𝕜 𝕎 2 ((0 : ℤ), (q : ℤ)))
    (y : mssE 𝕜 𝕎 2 ((s : ℤ), (0 : ℤ))) :
    mssMul 𝕜 𝕎 2 ((0 : ℤ), (q : ℤ)) ((s : ℤ), (0 : ℤ))
        ((s : ℤ), (q : ℤ)) h1 x y
      = (-1 : 𝕜) ^ (s * q) •
        mssMul 𝕜 𝕎 2 ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ))
          ((s : ℤ), (q : ℤ)) h2 y x := by
  -- the two cycles, transported to the honest page indices `(0, q)` and `(s, s)`
  set x₁ : pEraw 𝕜 𝕎 2 0 q :=
    pCast 𝕜 𝕎 2 (EI_pair 0 q) ((EN_pair 0 q).trans (Nat.zero_add q)) x with hx₁
  set y₁ : pEraw 𝕜 𝕎 2 s s :=
    pCast 𝕜 𝕎 2 (EI_pair s 0) ((EN_pair s 0).trans (Nat.add_zero s)) y with hy₁
  have hxinv : pCast 𝕜 𝕎 2 (EI_pair 0 q).symm
      ((EN_pair 0 q).trans (Nat.zero_add q)).symm x₁ = x := by
    rw [hx₁]
    exact mc_pCast_inv_apply (W := 𝕎) (EI_pair 0 q)
      ((EN_pair 0 q).trans (Nat.zero_add q)) x
  have hyinv : pCast 𝕜 𝕎 2 (EI_pair s 0).symm
      ((EN_pair s 0).trans (Nat.add_zero s)).symm y₁ = y := by
    rw [hy₁]
    exact mc_pCast_inv_apply (W := 𝕎) (EI_pair s 0)
      ((EN_pair s 0).trans (Nat.add_zero s)) y
  -- the index equalities at the two ends of the transports
  have hH1 : 0 + s = EI ((0 : ℤ), (q : ℤ)) + EI ((s : ℤ), (0 : ℤ)) := by
    rw [show EI ((0 : ℤ), (q : ℤ)) = 0 from EI_pair 0 q,
      show EI ((s : ℤ), (0 : ℤ)) = s from EI_pair s 0]
  have hH1' : q + s = EN ((0 : ℤ), (q : ℤ)) + EN ((s : ℤ), (0 : ℤ)) := by
    rw [show EN ((0 : ℤ), (q : ℤ)) = 0 + q from EN_pair 0 q,
      show EN ((s : ℤ), (0 : ℤ)) = s + 0 from EN_pair s 0]
    omega
  have hH2 : s + 0 = EI ((s : ℤ), (0 : ℤ)) + EI ((0 : ℤ), (q : ℤ)) := by
    rw [show EI ((s : ℤ), (0 : ℤ)) = s from EI_pair s 0,
      show EI ((0 : ℤ), (q : ℤ)) = 0 from EI_pair 0 q]
  have hH2' : s + q = EN ((s : ℤ), (0 : ℤ)) + EN ((0 : ℤ), (q : ℤ)) := by
    rw [show EN ((s : ℤ), (0 : ℤ)) = s + 0 from EN_pair s 0,
      show EN ((0 : ℤ), (q : ℤ)) = 0 + q from EN_pair 0 q]
    omega
  -- naturality of `pd_mul` under the two transports
  have hnat1 : pCast 𝕜 𝕎 2 hH1 hH1' (pd_mul 2 0 q s s x₁ y₁)
      = pd_mul 2 (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))
          (EI ((s : ℤ), (0 : ℤ))) (EN ((s : ℤ), (0 : ℤ))) x y := by
    have h := pd_mul_pCast_apply 𝕜 𝕎 2 0 q s s
      (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))
      (EI ((s : ℤ), (0 : ℤ))) (EN ((s : ℤ), (0 : ℤ)))
      (EI_pair 0 q).symm ((EN_pair 0 q).trans (Nat.zero_add q)).symm
      (EI_pair s 0).symm ((EN_pair s 0).trans (Nat.add_zero s)).symm hH1 hH1' x₁ y₁
    rw [hxinv, hyinv] at h
    exact h
  have hnat2 : pCast 𝕜 𝕎 2 hH2 hH2' (pd_mul 2 s s 0 q y₁ x₁)
      = pd_mul 2 (EI ((s : ℤ), (0 : ℤ))) (EN ((s : ℤ), (0 : ℤ)))
          (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) y x := by
    have h := pd_mul_pCast_apply 𝕜 𝕎 2 s s 0 q
      (EI ((s : ℤ), (0 : ℤ))) (EN ((s : ℤ), (0 : ℤ)))
      (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))
      (EI_pair s 0).symm ((EN_pair s 0).trans (Nat.add_zero s)).symm
      (EI_pair 0 q).symm ((EN_pair 0 q).trans (Nat.zero_add q)).symm hH2 hH2' y₁ x₁
    rw [hyinv, hxinv] at h
    exact h
  -- the two products, rewritten through the transports
  have e1 : mssMul 𝕜 𝕎 2 ((0 : ℤ), (q : ℤ)) ((s : ℤ), (0 : ℤ))
        ((s : ℤ), (q : ℤ)) h1 x y
      = pCast 𝕜 𝕎 2 (congrArg EI h1) (congrArg EN h1)
          (pCast 𝕜 𝕎 2 (EI_add (Enn_pair 0 q) (Enn_pair s 0))
            (EN_add (Enn_pair 0 q) (Enn_pair s 0))
            (pd_mul 2 (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))
              (EI ((s : ℤ), (0 : ℤ))) (EN ((s : ℤ), (0 : ℤ))) x y)) :=
    mssMul_apply_pos 𝕜 𝕎 2 (Enn_pair 0 q) (Enn_pair s 0) h1 x y
  rw [← hnat1] at e1
  have e2 : mssMul 𝕜 𝕎 2 ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ))
        ((s : ℤ), (q : ℤ)) h2 y x
      = pCast 𝕜 𝕎 2 (congrArg EI h2) (congrArg EN h2)
          (pCast 𝕜 𝕎 2 (EI_add (Enn_pair s 0) (Enn_pair 0 q))
            (EN_add (Enn_pair s 0) (Enn_pair 0 q))
            (pd_mul 2 (EI ((s : ℤ), (0 : ℤ))) (EN ((s : ℤ), (0 : ℤ)))
              (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) y x)) :=
    mssMul_apply_pos 𝕜 𝕎 2 (Enn_pair s 0) (Enn_pair 0 q) h2 y x
  rw [← hnat2] at e2
  -- the left hand side as a single transport of the clean product
  have eL : mssMul 𝕜 𝕎 2 ((0 : ℤ), (q : ℤ)) ((s : ℤ), (0 : ℤ))
        ((s : ℤ), (q : ℤ)) h1 x y
      = (-1 : 𝕜) ^ (q * s) • pCast 𝕜 𝕎 2
          ((Nat.add_comm 0 s).symm.trans
            ((hH1.trans (EI_add (Enn_pair 0 q) (Enn_pair s 0))).trans (congrArg EI h1)))
          ((Nat.add_comm q s).symm.trans
            ((hH1'.trans (EN_add (Enn_pair 0 q) (Enn_pair s 0))).trans (congrArg EN h1)))
          (pd_mul 2 s s 0 q y₁ x₁) := by
    have s1 : mssMul 𝕜 𝕎 2 ((0 : ℤ), (q : ℤ)) ((s : ℤ), (0 : ℤ))
          ((s : ℤ), (q : ℤ)) h1 x y
        = pCast 𝕜 𝕎 2
            ((hH1.trans (EI_add (Enn_pair 0 q) (Enn_pair s 0))).trans (congrArg EI h1))
            ((hH1'.trans (EN_add (Enn_pair 0 q) (Enn_pair s 0))).trans (congrArg EN h1))
            (pd_mul 2 0 q s s x₁ y₁) := by
      rw [e1, pCast_comp_apply, pCast_comp_apply]
    rw [s1, ← mc_pCast_inv_apply (Nat.add_comm 0 s) (Nat.add_comm q s)
        (pd_mul 2 0 q s s x₁ y₁), pCast_comp_apply,
      mc_pd_mul_comm 𝕜 E B p s q x₁ y₁, map_smul]
  -- the right hand side as a single transport of the clean product
  have eR : mssMul 𝕜 𝕎 2 ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ))
        ((s : ℤ), (q : ℤ)) h2 y x
      = pCast 𝕜 𝕎 2
          ((hH2.trans (EI_add (Enn_pair s 0) (Enn_pair 0 q))).trans (congrArg EI h2))
          ((hH2'.trans (EN_add (Enn_pair s 0) (Enn_pair 0 q))).trans (congrArg EN h2))
          (pd_mul 2 s s 0 q y₁ x₁) := by
    rw [e2, pCast_comp_apply, pCast_comp_apply]
  -- the two transports have the same endpoints
  have hfinal : pCast 𝕜 𝕎 2
        ((Nat.add_comm 0 s).symm.trans
          ((hH1.trans (EI_add (Enn_pair 0 q) (Enn_pair s 0))).trans (congrArg EI h1)))
        ((Nat.add_comm q s).symm.trans
          ((hH1'.trans (EN_add (Enn_pair 0 q) (Enn_pair s 0))).trans (congrArg EN h1)))
        (pd_mul 2 s s 0 q y₁ x₁)
      = pCast 𝕜 𝕎 2
          ((hH2.trans (EI_add (Enn_pair s 0) (Enn_pair 0 q))).trans (congrArg EI h2))
          ((hH2'.trans (EN_add (Enn_pair s 0) (Enn_pair 0 q))).trans (congrArg EN h2))
          (pd_mul 2 s s 0 q y₁ x₁) :=
    mc_pCast_congr_apply (W := 𝕎) _ _ _ _ (pd_mul 2 s s 0 q y₁ x₁)
  rw [eL, hfinal, eR, Nat.mul_comm q s]

/-- **Mixed graded commutativity of the second page** (the requested lemma). -/

theorem mixedComm (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) :
    ∀ (s q : ℕ) (hs : s ≤ N) (hq : q ≤ N) (b : Work.Pi6.Coh 𝕜 B s)
      (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q),
      Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ((s : ℤ), (0 : ℤ))
          ((s : ℤ), (q : ℤ)) (by ext <;> simp)
          (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin q f)
          (Work.Pi6.MSS.e2Row 𝕜 p s b) =
        (-1 : 𝕜) ^ (s * q) •
          Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ))
            ((s : ℤ), (q : ℤ)) (by ext <;> simp)
            (Work.Pi6.MSS.e2Row 𝕜 p s b)
            (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin q f) := by
  intro s q _ _ b f
  exact mc_mssMul_mixed 𝕜 E B p s q (by ext <;> simp) (by ext <;> simp)
    (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin q f)
    (Work.Pi6.MSS.e2Row 𝕜 p s b)

end

end Work.Pi6.MSS
