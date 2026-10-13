/-
  WilG4c / `CritFixAux.Pre` — the vocabulary and the elementary halves of the proof of
  `Work.WilkG4c.CritFixGoodMem`.

  Contents:
  * `mem_contSet_iff`: the value condition `contSet` is continuity of the fibre;
  * `AlDgListSlice_subset_CritFix`: the honest slice derivative graph satisfies the corrected
    criterion (no hypothesis on `L`);
  * `parPt_append'`, `cubePt_append'`, `jointDeriv_eq_fibreDeriv`: on the joint `C^m`-locus the
    joint derivative along the lifted cube directions is the fibre derivative;
  * `parEq_mem`, `fibreJBad_mem`: the parameter restriction `{parPt = l}` and the fibre of the
    joint bad locus over `l` are `Ω`-definable.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.CritFixDefs
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.MemContSet
import Submission.Work.WilG4c.SliceDerivJointSubset
import Submission.Work.WilG4c.JBadMem
import Submission.Work.WilG4c.iterDir_famFunHat_xPt
import Submission.Work.WilG4c.CritFixAux.LimeqFibreDeriv
import Submission.Work.WilG4c.DensePunctureCriterion
import Submission.Work.WilG4b.projCoords_mem
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.API

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilkG4c

open WilkiesDesign

/-! ## 1. The value condition `contSet` is continuity of the fibre -/

/-- `contSet p n f` is exactly the set of `w` at which the fibre `y ↦ f (parPt w) y` is
continuous at `cubePt w`.  One direction is `MemContSet`; the other unpacks the punctured limit
(which, together with the graph membership at the limit value, is continuity). -/
theorem mem_contSet_iff {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (w : Fin (p + (n + 1)) → ℝ) :
    w ∈ contSet p n f ↔ ContinuousAt (fun y : Fin (n + 1) → ℝ => f (parPt w) y) (cubePt w) := by
  constructor
  · rintro ⟨s, hs1, hs2⟩
    -- `Fin.snoc w s ∈ famGraph f` forces `s = f (parPt w) (cubePt w)`.
    have hs : s = f (parPt w) (cubePt w) := by
      have h := hs2
      rw [famGraph_eq_graphOf_famFunHat] at h
      simpa [graphOf, famFunHat_eq_parPt_cubePt] using h
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hs1 (ε / 2) (by linarith)
    simp only [Fin.init_snoc, Fin.snoc_last] at hδ
    refine ⟨δ, hδpos, fun x hx => ?_⟩
    rcases eq_or_ne x (cubePt w) with rfl | hne
    · rw [dist_self]; exact hε
    · have hcomp : ∀ j : Fin (n + 1), |x j - cubePt w j| < δ := by
        intro j
        rw [← Real.dist_eq]
        exact (dist_pi_lt_iff hδpos).mp hx j
      have hmem : (Fin.snoc (Fin.append (parPt w) x) (f (parPt w) x)
          : Fin (p + (n + 1) + 1) → ℝ) ∈ WilkiesDesign.CG.famGraph f := by
        rw [famGraph_eq_graphOf_famFunHat, graphOf, Set.mem_ofPred_eq]
        rw [Fin.init_snoc, Fin.snoc_last]
        exact (Work.WilG4c.famFunHat_append f (parPt w) x).symm
      have hle := hδ x hne hcomp (f (parPt w) x) hmem
      rw [hs] at hle
      rw [Real.dist_eq]
      linarith
  · intro h
    exact Work.WilG4c.MemContSet f w h

/-- The last coordinate of a `Fin.snoc` (with the constant family `ℝ`). -/
theorem snoc_last_real {N : ℕ} (w : Fin N → ℝ) (a : ℝ) :
    (Fin.snoc w a : Fin (N + 1) → ℝ) (Fin.last N) = a := by
  simp [Fin.snoc]

/-- Rebuilding a vector from its `Fin.init` and its last coordinate. -/
theorem snoc_init_self_real {N : ℕ} (z : Fin (N + 1) → ℝ) :
    (Fin.snoc (Fin.init z) (z (Fin.last N)) : Fin (N + 1) → ℝ) = z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Fin.snoc]
  · simp [Fin.snoc, Fin.init]

/-- `Fin.init` forgets a `Fin.snoc` (with the constant family `ℝ`). -/
theorem init_snoc_real {N : ℕ} (w : Fin N → ℝ) (a : ℝ) :
    Fin.init (Fin.snoc w a : Fin (N + 1) → ℝ) = w := by
  funext i
  simp [Fin.snoc, Fin.init]

/-! ## 2. `AlDgListSlice ⊆ CritFix` -/

/-- Membership in `CritFix` unfolds to the localised criterion together with the value
condition. -/
theorem mem_CritFix_iff {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (n + 1))} {z : Fin (p + (n + 1) + 1) → ℝ} :
    z ∈ CritFix p n f L ↔
      z ∈ LocCritFix p n f L ∧
        z ∈ Work.WilG4c.LimeqP p n (dgSet p n f L.length (fun j => L.get j)) :=
  Iff.rfl

/-- **The honest fibre derivative graph is contained in the corrected criterion.**  No hypothesis
on `L` is needed: for `L = []` the criterion contains no limit conditions, and `ContDiffAt ℝ 0`
is continuity on a neighbourhood, so the argument is uniform. -/
theorem AlDgListSlice_subset_CritFix {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) :
    AlDgListSlice p n f L ⊆ CritFix p n f L := by
  intro z hz
  rw [mem_AlDgListSlice] at hz
  obtain ⟨hg, hval⟩ := hz
  obtain ⟨ρ, hρpos, hρball⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : Fin (n + 1) → ℝ,
      dist y (cubePt (Fin.init z)) < ρ →
      ContDiffAt ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y := by
    have hev : ∀ᶠ y in 𝓝 (cubePt (Fin.init z)),
        ContDiffAt ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y) y :=
      hg.eventually (by simp)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, h⟩ := hev
    exact ⟨ε, hε, fun y hy => h hy⟩
  rw [mem_CritFix_iff]
  constructor
  · refine ⟨ρ, hρpos, ?_⟩
    intro w' hpar hdist
    have hw'slice : ContDiffAt ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt w') y)
        (cubePt w') := by
      have h1 := hρball (cubePt w') hdist
      simpa [hpar] using h1
    refine ⟨Work.WilG4c.MemContSet f w' hw'slice.continuousAt, ?_⟩
    rw [Set.mem_iInter₂]
    intro i _
    simp only [LimCond, ProjLim, WilkiesDesign.projLast, Set.mem_ofPred_eq]
    refine ⟨_, Work.WilkG4c.CritFixAux.LimeqFibreDeriv f w'
      (cntWord n (i.1.val + 1) (fun j => (i.2 j).val)) ?_⟩
    exact hw'slice.of_le (by exact_mod_cast Nat.succ_le_of_lt i.1.isLt)
  · have hmain := Work.WilkG4c.CritFixAux.LimeqFibreDeriv f (Fin.init z)
      (fun j : Fin L.length => L.get j) hg
    have hz_eq : Fin.snoc (Fin.init z)
        (iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
          (cubePt (Fin.init z)) (fun j => Pi.single (L.get j) 1)) = z := by
      rw [← hval]
      exact Fin.snoc_init_self z
    rwa [hz_eq] at hmain

/-! ## 3. Joint and fibre iterated derivatives agree on the joint good locus -/

/-- The parameter part of `Fin.append l x` is `l`. -/
theorem parPt_append' {p n : ℕ} (l : Fin p → ℝ) (x : Fin (n + 1) → ℝ) :
    parPt (Fin.append l x) = l := by
  funext i
  simp [parPt, Fin.append_left]

/-- The cube part of `Fin.append l x` is `x`. -/
theorem cubePt_append' {p n : ℕ} (l : Fin p → ℝ) (x : Fin (n + 1) → ℝ) :
    cubePt (Fin.append l x) = x := by
  funext j
  simp [cubePt, Fin.append_right]

theorem iteratedFDeriv_congr_index {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m m' : ℕ} (h : m = m') (f : E → ℝ) (x : E) (v : Fin m → E) (w : Fin m' → E)
    (hw : ∀ i : Fin m, w (Fin.cast h i) = v i) :
    iteratedFDeriv ℝ m f x v = iteratedFDeriv ℝ m' f x w := by
  subst h
  congr 1
  funext i
  exact (hw i).symm

/-- `iterDir` along a list of coordinate directions is the evaluated iterated derivative. -/
private lemma iterDir_ofFn_list {N m : ℕ} (v : Fin m → Fin N) (G : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) (hG : ContDiffAt ℝ m G z) :
    iterDir (List.ofFn v) G z = iteratedFDeriv ℝ m G z (fun k => Pi.single (v k) 1) := by
  have hG' : ContDiffAt ℝ (List.ofFn v).length G z := by
    rw [List.length_ofFn]; exact hG
  rw [Work.WilG4c.iterDir_eq_iteratedFDeriv (List.ofFn v) G z hG']
  refine iteratedFDeriv_congr_index List.length_ofFn G z
    (fun k => Pi.single ((List.ofFn v).get k) 1) (fun k => Pi.single (v k) 1) (fun i => ?_)
  congr 1
  rw [List.get_ofFn]

/-- The same as `iterDir_ofFn_list`, with the directions pushed forward along a map of
coordinates. -/
private lemma iterDir_ofFn_map' {N M m : ℕ} (φ : Fin M → Fin N) (V : Fin m → Fin M)
    (G : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) (hG : ContDiffAt ℝ m G z) :
    iterDir ((List.ofFn V).map φ) G z = iteratedFDeriv ℝ m G z (fun k => Pi.single (φ (V k)) 1) := by
  rw [List.map_ofFn]
  exact iterDir_ofFn_list (fun k => φ (V k)) G z hG

/-- **Joint implies fibre, derivative values.**  If the joint function `famFunHat f` is `C^m` at
`Fin.append l x`, then the joint `m`-th derivative along the lifted cube directions is the fibre
`m`-th derivative of `y ↦ f l y` at `x` along the same directions. -/
theorem jointDeriv_eq_fibreDeriv {p n m : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (x : Fin (n + 1) → ℝ) (W : Fin m → Fin (n + 1))
    (hx : ContDiffAt ℝ m (famFunHat f) (Fin.append l x)) :
    iteratedFDeriv ℝ m (famFunHat f) (Fin.append l x)
        (fun k => Pi.single (Fin.natAdd p (W k)) 1)
      = iteratedFDeriv ℝ m (fun y : Fin (n + 1) → ℝ => f l y) x
          (fun k => Pi.single (W k) 1) := by
  rw [← iterDir_ofFn_map' (Fin.natAdd p) W (famFunHat f) (Fin.append l x) hx]
  have hz : Fin.init (Fin.snoc (Fin.append l x) (0 : ℝ) : Fin (p + (n + 1) + 1) → ℝ)
      ∈ interior {w | ContDiffAt ℝ (List.ofFn W).length (famFunHat f) w} := by
    rw [Fin.init_snoc, List.length_ofFn]
    exact mem_interior_iff_mem_nhds.mpr (hx.eventually (by simp))
  obtain ⟨hslice, hval⟩ := Work.WilG4c.SliceDerivJointSubset f (List.ofFn W)
    (Fin.snoc (Fin.append l x) (0 : ℝ) : Fin (p + (n + 1) + 1) → ℝ) hz
  simp only [Fin.init_snoc, parPt_append', cubePt_append'] at hval hslice
  rw [hval]
  have hslice' : ContDiffAt ℝ m (fun y : Fin (n + 1) → ℝ => f l y) x := by
    simpa only [List.length_ofFn, Fintype.card_fin] using hslice
  rw [← Work.WilG4c.iterDir_eq_iteratedFDeriv (List.ofFn W)
    (fun y : Fin (n + 1) → ℝ => f l y) x hslice]
  exact iterDir_ofFn_list W (fun y : Fin (n + 1) → ℝ => f l y) x hslice'

/-! ## 4. The fibre of the joint bad locus over a parameter is `Ω`-definable -/

/-- The parameter restriction `{w | parPt w = l}` is `Ω`-definable, uniformly in `l`: it is the
intersection of the coordinate hyperplanes `w (castAdd N i) = l i`, each of which is the zero set
of a polynomial of total degree one. -/
theorem parEq_mem (S : WilkiesDesign.SOMin) (p N : ℕ) :
    ∃ (F D : ℕ), ∀ (l : Fin p → ℝ),
      {w : Fin (p + N) → ℝ | (fun i : Fin p => w (Fin.castAdd N i)) = l}
        ∈ S.Ω F D (p + N) := by
  refine ⟨p + N + 1, ∑ _i : Fin p, 1, fun l => ?_⟩
  have hset : {w : Fin (p + N) → ℝ | (fun i : Fin p => w (Fin.castAdd N i)) = l}
      = ⋂ i : Fin p, {w : Fin (p + N) → ℝ | w (Fin.castAdd N i) = l i} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h i => congrFun h i, fun h => funext h⟩
  rw [hset]
  refine S.inter (F := p + N) (n := p + N) (k := p) (fun _ => 1)
    (fun i => {w : Fin (p + N) → ℝ | w (Fin.castAdd N i) = l i}) ?_
  intro i
  have h := Work.WilG1.Omega.hyp_mem (S := S) (n := p + N) 0
    (MvPolynomial.X (Fin.castAdd N i) - MvPolynomial.C (l i))
  have hz : {x : Fin (p + N) → ℝ | MvPolynomial.eval x
        (MvPolynomial.X (Fin.castAdd N i) - MvPolynomial.C (l i)) = 0}
      = {w : Fin (p + N) → ℝ | w (Fin.castAdd N i) = l i} := by
    ext w
    simp [sub_eq_zero]
  rw [hz] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  have h1 : (MvPolynomial.X (Fin.castAdd N i) - MvPolynomial.C (l i) :
      MvPolynomial (Fin (p + N)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub_C_le _ _) ?_
    rw [MvPolynomial.totalDegree_X]
  simpa using h1

/-- **The fibre of the joint bad locus.**  For a family `f` and a parameter `l`, the set of cube
points `x` such that `(l,x)` lies in the joint bad locus `jBad p n f k` is `Ω`-definable: it is
the image of `jBad p n f k ∩ {parPt = l}` under the coordinate projection onto the cube. -/
theorem fibreJBad_mem (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (p n F0 D k : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ)
    (hf : WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1)) :
    ∃ (F D' : ℕ),
      {x : Fin (n + 1) → ℝ | Fin.append l x ∈ jBad p n f k} ∈ S.Ω F D' (n + 1) := by
  obtain ⟨aJ, bJ, hJ⟩ := Work.WilG4c.JBadMem S hder p n F0
  obtain ⟨aP, DP, hP⟩ := parEq_mem S p (n + 1)
  obtain ⟨-, hJbad⟩ := hJ D k f hf
  obtain ⟨K, pdeg, hK⟩ := Work.WilG4b.projCoords_mem (S := S) (m := p + (n + 1)) (N := n + 1)
    (Fin.natAdd p)
  refine ⟨max aJ aP + 1 + K, pdeg.eval (bJ.eval ![D, k] + DP), ?_⟩
  have hJbad' : jBad p n f k ∈ S.Ω (max aJ aP) (bJ.eval ![D, k]) (p + (n + 1)) :=
    Work.WilG1.Omega.mono hJbad (le_max_left _ _) le_rfl
  have hPl : {w : Fin (p + (n + 1)) → ℝ |
        (fun i : Fin p => w (Fin.castAdd (n + 1) i)) = l}
      ∈ S.Ω (max aJ aP) DP (p + (n + 1)) :=
    Work.WilG1.Omega.mono (hP l) (le_max_right _ _) le_rfl
  have hXmem : (jBad p n f k ∩ {w : Fin (p + (n + 1)) → ℝ |
        (fun i : Fin p => w (Fin.castAdd (n + 1) i)) = l})
      ∈ S.Ω (max aJ aP + 1) (bJ.eval ![D, k] + DP) (p + (n + 1)) :=
    Work.WilG0.Omega_inter2 hJbad' hPl
  have himg := hK (max aJ aP + 1) (bJ.eval ![D, k] + DP)
    (jBad p n f k ∩ {w : Fin (p + (n + 1)) → ℝ |
      (fun i : Fin p => w (Fin.castAdd (n + 1) i)) = l}) hXmem
  have hset : {y : Fin (n + 1) → ℝ |
        ∃ x ∈ jBad p n f k ∩ {w : Fin (p + (n + 1)) → ℝ |
          (fun i : Fin p => w (Fin.castAdd (n + 1) i)) = l}, y = x ∘ Fin.natAdd p}
      = {x : Fin (n + 1) → ℝ | Fin.append l x ∈ jBad p n f k} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxj, hxp⟩ := hx
      have hsplit : x = Fin.append l (fun j : Fin (n + 1) => x (Fin.natAdd p j)) := by
        rw [← hxp, Fin.append_castAdd_natAdd]
      change Fin.append l (fun j : Fin (n + 1) => x (Fin.natAdd p j)) ∈ jBad p n f k
      rw [← hsplit]
      exact hxj
    · intro hy
      refine ⟨Fin.append l y, ⟨hy, ?_⟩, ?_⟩
      · funext i
        simp [parPt, Fin.append_left]
      · funext j
        simp only [Function.comp_apply, Fin.append_right, cubePt_apply]
  rw [hset] at himg
  exact himg

end Work.WilkG4c
