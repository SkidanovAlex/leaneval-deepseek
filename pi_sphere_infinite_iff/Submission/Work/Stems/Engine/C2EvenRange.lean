import Mathlib
import Submission.Work.Stems.Engine.C2Range
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.Stems.Engine.C2Even
import Submission.Work.Stems.ratH_conn_piIso
import Submission.Work.Stems.homotopyGroup_loop
import Submission.Work.Stems.homotopyFibre_evalOne_equiv_loop
import Submission.Work.Stems.ratH_isEMSpace_self
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.RatHurewicz.SimplyConnectedBridge
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.gysinCupIsoReduction

/-!
# The `C2` even step with a **free top** (range models)

`Work.Stems.Engine.c2evenRange_of_oddSphereRange` (`Engine/C2Even.lean`) proves the range-form even
step of the `C2` layer for *genuine* models of `K(ℤ,2j)`.  The free-top sphere route of area
RATHUREWICZ (`Submission/Work/RatHurewicz/coverRouteFreeTop.lean`) instead consumes *range* models
(`Work.Serre.serreC0Range`, proved), so it needs the even step for a range model of `K(ℤ,2j)`
through degree `M`, with the bound `4j - 1` of the periodicity and the hypothesis
`M ≥ 2(2j-1) = 4j-2` (which is exactly what the fibre `ΩL` — a range model of `K(ℤ,2j-1)` through
`M-1` — needs in order to be known as a rational sphere).

The mathematical content is `Work.RatHurewicz.RangeModelRatAcyclic` (the rational homology of a
range model of `K(ℤ,k)` through `2k-1`) together with the Hurewicz generator
`Work.Stems.ratH_iso_rat_of_conn_piIso`, and the engine is the path–loop fibration with the Gysin /
periodicity statement `Work.Serre.SerreE3b`.  As in `C2Even.lean`, the periodicity is proved in
cohomology and transported back by the field universal coefficient theorem.

Note the *bound*: the periodicity `⌣e : H^m(L) ≅ H^{m+2j}(L)` is available for `m ≤ 2j-2` because
the fibre `ΩL` is known as a rational sphere only through degree `2(2j-1)-1 = 4j-3`; hence the
conclusions are capped at `d < 4j-1` — the free top `M` enters only through the hypothesis
`4j-2 ≤ M`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The homotopy groups at equal indices are isomorphic** (transport of the index). -/
noncomputable def piMulEquivOfIndexEq {X : Type} [TopologicalSpace X] {x : X} {a b : ℕ}
    (h : a = b) [Nonempty (Fin a)] [Nonempty (Fin b)] :
    HomotopyGroup (Fin a) X x ≃* HomotopyGroup (Fin b) X x := by
  cases h
  exact MulEquiv.refl _

/-- **The loop space of a range model of `K(A,k+1)` is a range model of `K(A,k)`**, with the range
`M - 1` (the loop shift `π_i(ΩX) ≅ π_{i+1}(X)`). -/
theorem isEMSpaceUpTo_loop {A : Type} [AddCommGroup A] {k M : ℕ} (hk : 1 ≤ k) {X : Type}
    [TopologicalSpace X] (pt : X)
    (h : Work.Serre.IsEMSpaceUpTo A (k + 1) (Nat.succ_pos k) M X pt) :
    Work.Serre.IsEMSpaceUpTo A k (by omega) (M - 1) (Path pt pt) (Path.refl pt) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := Work.Stems.homotopyGroup_loop (X := X) (n := k) pt
    exact ⟨e.symm.trans h.1.some⟩
  · intro i hi hdisj
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · let e := Work.Stems.curryEquivGroup (X := X) (x := pt) 0
      have h1 : ∀ x y : HomotopyGroup (Fin 1) X pt, x = y :=
        fun x y => (h.2 1 (by omega) (Or.inl (by omega))).elim x y
      exact ⟨fun a b => by
        obtain ⟨x, rfl⟩ := e.surjective a
        obtain ⟨y, rfl⟩ := e.surjective b
        rw [h1 x y]⟩
    · haveI : Nonempty (Fin i) := ⟨⟨0, hipos⟩⟩
      obtain ⟨e⟩ := Work.Stems.homotopyGroup_loop (X := X) (n := i) pt
      have h1 : ∀ x y : HomotopyGroup (Fin (i + 1)) X pt, x = y :=
        fun x y => (h.2 (i + 1) (by omega)
          (hdisj.elim (fun h' => Or.inl (by omega)) (fun h' => Or.inr (by omega)))).elim x y
      exact ⟨fun a b => by
        obtain ⟨x, rfl⟩ := e.surjective a
        obtain ⟨y, rfl⟩ := e.surjective b
        rw [h1 x y]⟩

/-- **The loop space of a range model of `K(A,m)` is a range model of `K(A,m-1)`** (`m ≥ 2`), in
the index shape used below. -/
theorem isEMSpaceUpTo_loop' {A : Type} [AddCommGroup A] {m M : ℕ} (hm : 2 ≤ m) {X : Type}
    [TopologicalSpace X] (pt : X) (h : Work.Serre.IsEMSpaceUpTo A m (by omega) M X pt) :
    Work.Serre.IsEMSpaceUpTo A (m - 1) (by omega) (M - 1) (Path pt pt) (Path.refl pt) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel (by omega : 1 ≤ m)).symm⟩
  exact Work.Stems.isEMSpaceUpTo_loop (k := k) (by omega) pt h

end

end Work.Stems

namespace Work.Stems.Engine

noncomputable section

/-- **The even step of the `C2` layer for a range model with a free top** (`j ≥ 2`, top `M`).  A
range model `L` of `K(ℤ,2j)` through degree `M ≥ 4j-2` has the rational homology of `ℂP^∞`
rescaled by `2j` below degree `4j-1`: `H_{2jk}(L;ℚ) ≅ ℚ` and `H_d(L;ℚ) = 0` for `2j ∤ d`. -/
theorem c2evenRangeModel (h : Work.RatHurewicz.RangeModelRatAcyclic)
    (hE3b : Work.Serre.SerreE3b) {j : ℕ} (hj : 2 ≤ j) {M : ℕ} (hM : 2 * (2 * j - 1) ≤ M)
    {L : Type} [TopologicalSpace L] (l₀ : L)
    (hL : Work.Serre.IsEMSpaceUpTo ℤ (2 * j) (by omega) M L l₀) :
    (∀ k : ℕ, 2 * j * k < 4 * j - 1 →
        Nonempty (Work.Serre.ratH (TopCat.of L) (2 * j * k) ≅ ModuleCat.of ℚ ℚ)) ∧
      (∀ d : ℕ, d < 4 * j - 1 → (∀ k : ℕ, d ≠ 2 * j * k) →
        IsZero (Work.Serre.ratH (TopCat.of L) d)) := by
  haveI hpcL : PathConnectedSpace L :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero l₀ (hL.2 0 (by omega) (Or.inr (by omega)))
  have hscL : SimplyConnectedSpace L :=
    Work.RatHurewicz.simplyConnectedSpace_of_subsingleton l₀ (hL.2 0 (by omega) (Or.inr (by omega)))
      (hL.2 1 (by omega) (Or.inr (by omega)))
  -- connectivity of `L`
  have hLow : ∀ d : ℕ, 0 < d → d < 2 * j → IsZero (Work.Serre.ratH (TopCat.of L) d) := by
    intro d hd hd'
    have h' := Work.Serre.serreE0Range L l₀ (2 * j - 1)
      (fun i hi => hL.2 i (by omega) (Or.inr (by omega)))
    exact h' d hd (by omega)
  -- the fibre `ΩL = Path l₀ l₀` is a range model of `K(ℤ,2j-1)` through `M-1 ≥ 4j-3`
  have hFL : Work.Serre.IsEMSpaceUpTo ℤ (2 * j - 1) (by omega) (M - 1) (Path l₀ l₀)
      (Path.refl l₀) :=
    Work.Stems.isEMSpaceUpTo_loop' (m := 2 * j) (by omega) l₀ hL
  -- it is a rational sphere through degree `2(2j-1) - 1 = 4j-3`
  have hsphere : Work.Stems.Engine.RatSphereBelow (Path l₀ l₀) (2 * j - 1) (2 * (2 * j - 1)) := by
    refine ⟨?_, ?_⟩
    · -- the generator: `H_{2j-1}(ΩL;ℚ) ≅ ℚ` (Hurewicz in the first non-vanishing degree)
      haveI : Nonempty (Fin (2 * j - 1)) := ⟨⟨0, by omega⟩⟩
      haveI : Nonempty (Fin (2 * j)) := ⟨⟨0, by omega⟩⟩
      obtain ⟨e⟩ := Work.Stems.homotopyGroup_loop (X := L) (n := 2 * j - 1) l₀
      refine Work.Stems.ratH_iso_rat_of_conn_piIso (n := 2 * j - 1) (by omega) (Path.refl l₀)
        (⟨(e.symm.trans (Work.Stems.piMulEquivOfIndexEq (by omega : (2 * j - 1) + 1 = 2 * j))).trans
          hL.1.some⟩ : Nonempty (HomotopyGroup (Fin (2 * j - 1)) (Path l₀ l₀)
            (Path.refl l₀) ≃* Multiplicative ℤ)) (fun i hi => ?_)
      exact hFL.2 i (by omega) (Or.inl hi)
    · -- the vanishing: below `2j-1` by connectivity, above by `RangeModelRatAcyclic`
      intro j' hj' hjN hjn
      rcases lt_or_ge j' (2 * j - 1) with hsmall | hbig
      · have h' := Work.Serre.serreE0Range (Path l₀ l₀) (Path.refl l₀) (2 * j - 2)
          (fun i hi => hFL.2 i (by omega) (Or.inl (by omega)))
        exact h' j' hj' (by omega)
      · have hjn' : 2 * j - 1 < j' := lt_of_le_of_ne hbig (Ne.symm hjn)
        exact h (2 * j - 1) (by omega) (Path l₀ l₀) (Path.refl l₀)
          (fun i _ hin => hFL.2 i hin (by
            rcases lt_or_ge i (2 * j - 1) with hlt | hge
            · exact Or.inl hlt
            · exact Or.inr (by omega)))
          j' hjn' (by omega)
  -- transfer to the homotopy fibre of the path–loop fibration and apply `SerreE3b`
  obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop L l₀
  have hFib : ∀ t : ℕ, 0 < t → t ≠ 2 * j - 1 → t ≤ 2 * (2 * j - 1) - 1 →
      IsZero (Work.Serre.ratH
        (TopCat.of (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne L l₀)
          (Work.RatHurewicz.pathSpaceConst L l₀))) t) :=
    fun t ht htr htN =>
      Work.Stems.isZero_ratH_of_homotopyEquiv heq t (hsphere.2 t ht (by omega) htr)
  have hFibGen : Nonempty (Work.Serre.ratH
      (TopCat.of (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne L l₀)
        (Work.RatHurewicz.pathSpaceConst L l₀))) (2 * j - 1) ≅ ModuleCat.of ℚ ℚ) :=
    Work.Stems.isoRat_of_homotopyEquiv heq (2 * j - 1) hsphere.1
  haveI : ContractibleSpace (Work.StemsB.PathSpace L l₀) := Work.StemsB.contractible_pathSpace L l₀
  have hacyc : Work.Serre.RatAcyclic (Work.StemsB.PathSpace L l₀) :=
    Work.Serre.ratAcyclic_of_contractible (Work.StemsB.PathSpace L l₀)
  have hgysin : ∀ m : ℕ, m + (2 * j - 1) + 1 ≤ 2 * (2 * j - 1) →
      ∃ e : Work.Serre.ratCoh (TopCat.of L) (2 * j - 1 + 1),
        IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of L) (2 * j - 1 + 1) e m)) := by
    intro m hm
    exact hE3b (Work.StemsB.PathSpace L l₀) L (Work.StemsB.evalOne L l₀)
      (Work.RatHurewicz.pathSpaceConst L l₀) (2 * j - 1) (2 * (2 * j - 1) - 1) (by omega)
      (Work.StemsB.isSerreFibration_evalOne L l₀) hscL hacyc hFib hFibGen m (by omega)
  have hperStep : ∀ m : ℕ, m ≤ 2 * j - 2 → IsZero (Work.Serre.ratCoh (TopCat.of L) m) →
      IsZero (Work.Serre.ratCoh (TopCat.of L) (m + 2 * j)) := by
    intro m hm hzero
    obtain ⟨e, he⟩ := hgysin m (by omega)
    haveI := he
    have hdeg : m + ((2 * j - 1) + 1) = m + 2 * j := by omega
    have hiso : Work.Serre.ratCoh (TopCat.of L) (m + ((2 * j - 1) + 1)) ≅
        Work.Serre.ratCoh (TopCat.of L) (m + 2 * j) :=
      eqToIso (congrArg (Work.Serre.ratCoh (TopCat.of L)) hdeg)
    exact IsZero.of_iso hzero
      ((asIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of L) (2 * j - 1 + 1) e m))).trans
        hiso).symm
  have hcoh : ∀ d : ℕ, d < 4 * j - 1 → (∀ k : ℕ, d ≠ 2 * j * k) →
      IsZero (Work.Serre.ratCoh (TopCat.of L) d) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd hne
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · exact absurd rfl (hne 0)
      · rcases Nat.lt_or_ge d (2 * j) with hsmall | hbig
        · exact Work.Serre.isZero_ratCoh_of_isZero_ratH_dup (hLow d hpos hsmall)
        · have hd' : d - 2 * j < 4 * j - 1 := by omega
          have hne' : ∀ k : ℕ, d - 2 * j ≠ 2 * j * k := by
            intro k hk
            exact hne (k + 1) (by rw [Nat.mul_succ, ← hk]; omega)
          have hm' : d - 2 * j ≤ 2 * j - 2 := by omega
          have hsum : (d - 2 * j) + 2 * j = d := by omega
          exact hsum ▸ hperStep (d - 2 * j) hm' (ih (d - 2 * j) (by omega) hd' hne')
  refine ⟨?_, ?_⟩
  · intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simpa using Work.Serre.ratH_zero_of_pathConnected L
    · have hk1 : k = 1 := by
        by_contra hk1
        have h2 : 2 ≤ k := by omega
        have hle : 2 * j * 2 ≤ 2 * j * k := Nat.mul_le_mul_left (2 * j) h2
        omega
      subst hk1
      haveI : Nonempty (Fin (2 * j)) := ⟨⟨0, by omega⟩⟩
      simpa using Work.Stems.ratH_iso_rat_of_conn_piIso (n := 2 * j) (by omega) l₀ hL.1
        (fun i hi => hL.2 i (by omega) (by omega))
  · intro d hd hne
    exact Work.Stems.isZero_ratH_of_isZero_ratCoh (hcoh d (by omega) hne)

/-- **The interface of the free-top even step**: the *vanishing* conjunct of `c2evenRangeModel` as
a `Prop`, which is what the free-top odd step (the acyclicity of the cover of `Sⁿ`) consumes. -/
def C2evenRangeModelVanishing : Prop :=
  ∀ (j : ℕ) (hj : 2 ≤ j) (M : ℕ), 2 * (2 * j - 1) ≤ M →
    ∀ (L : Type) [TopologicalSpace L] (l₀ : L),
      Work.Serre.IsEMSpaceUpTo ℤ (2 * j) (by omega) M L l₀ →
      ∀ d : ℕ, d < 4 * j - 1 → (∀ k : ℕ, d ≠ 2 * j * k) →
        IsZero (Work.Serre.ratH (TopCat.of L) d)

/-- **The free-top even step, in interface form.** -/
theorem c2evenRangeModelVanishing (h : Work.RatHurewicz.RangeModelRatAcyclic)
    (hE3b : Work.Serre.SerreE3b) : C2evenRangeModelVanishing :=
  fun j hj M hM L _ l₀ hL =>
    (c2evenRangeModel h hE3b hj hM l₀ hL).2

/-- **The free-top odd step of `C2`, in the range the free-top sphere route uses.**  For odd `n ≥ 3`,
a *range model* `X` of `K(ℤ,n)` through degree `N ≥ 2n-3`, and a `πₙ`-bijective map
`f : Sⁿ → X`, the homotopy fibre of `f` — the `(n-1)`-connected cover of `Sⁿ` — is rationally
acyclic in every degree `0 < j ≤ M`, for every `M ≤ 2n-4`.

The cap `M ≤ 2n-4` is intrinsic to the engine: the periodicity that produces the rational homology
of the fibre `ΩX = K(ℤ,n-1)` reaches only degree `2(n-1)-1 = 2n-3` (see the discussion in
`Submission/Work/Stems/EM_C2_RANGE_FINDING.md` and the bound of `C2evenRange`), so the long exact
sequence of the fibration `E → Sⁿ` sees the fibre one degree short.  The sphere route consumes
exactly `M = 2n-4`. -/
def OddCoverAcyclicRange : Prop :=
  ∀ (n M N : ℕ) (hn : 3 ≤ n), Odd n → M ≤ 2 * n - 4 → 2 * n - 3 ≤ N →
    ∀ (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X pt →
      ∀ (s₀ : Work.Serre.Sph n) (f : C(Work.Serre.Sph n, X)),
        Function.Bijective (Work.Serre.piMapN f n s₀) →
        ∀ j : ℕ, 0 < j → j ≤ M →
          IsZero (Work.Serre.ratH
            (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) j)

end

end Work.Stems.Engine
