import Mathlib
import Submission.Work.Serre.RangeEMVanFinDefs
import Submission.Work.Serre.serreS1OfRangeEMVan
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.serreConnectedCover
import Submission.Work.Serre.serreE3a
import Submission.Work.Serre.E3aModel
import Submission.Work.Serre.serreK2Proved
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.piMapN_monoidHom
import Submission.Work.Stems.isHurewiczFibration_homotopyFibreFst
import Submission.Work.RatHurewicz.RelHomotopy

namespace Work.Rat

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy unitInterval

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

noncomputable section

/-- **The general mapping theorem (any map, not just a fibration).**  If `p : E → B` has
path-connected target and rationally acyclic homotopy fibre in degrees `≤ N`, then `p` induces an
isomorphism on rational homology in degrees `< N`.

This is `Work.Serre.serreE3aStepA` with the hypothesis "`p` is a Serre fibration" removed: the map
is replaced by `mpathQ p`, which is a Serre fibration for *every* `p`. -/
theorem isRatHomologyIso_of_ratAcyclicBelow_homotopyFibre {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (N : ℕ) (hB : PathConnectedSpace B)
    (h : Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre p e₀) N) :
    ∀ i : ℕ, i < N → IsIso (Work.Serre.ratHomologyMap p i) := by
  have hq : Work.StemsB.IsSerreFibration (Work.Serre.mpathQ p) :=
    Work.Serre.mpathQ_isSerreFibration p
  have hfib : ∀ t : ℕ, 0 < t → t ≤ N →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (Work.Serre.mpathQ p) (p e₀))) t) := by
    intro t ht htN
    obtain ⟨e⟩ := Work.Serre.mpathQ_fibreHomeo p e₀
    haveI : IsIso (Work.Serre.ratHomologyMap (e.toHomotopyEquiv.toFun) t) :=
      Work.Serre.IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv t
    exact IsZero.of_iso (h.1 t ht htN) (asIso (Work.Serre.ratHomologyMap (e.toHomotopyEquiv.toFun) t))
  have h0 : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (Work.Serre.mpathQ p) (p e₀))) 0
      ≅ ModuleCat.of ℚ ℚ) := by
    obtain ⟨e⟩ := Work.Serre.mpathQ_fibreHomeo p e₀
    haveI : IsIso (Work.Serre.ratHomologyMap (e.toHomotopyEquiv.toFun) 0) :=
      Work.Serre.IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv 0
    haveI : IsIso (Work.Serre.ratHomologyMap (Work.Serre.toPoint (Work.RatHurewicz.homotopyFibre p e₀)) 0) := h.2
    refine ⟨(asIso (Work.Serre.ratHomologyMap (e.toHomotopyEquiv.toFun) 0)).trans ?_⟩
    exact (asIso (Work.Serre.ratHomologyMap (Work.Serre.toPoint (Work.RatHurewicz.homotopyFibre p e₀)) 0)).trans
      (Work.Serre.ratH_zero_of_pathConnected PUnit).some
  intro i hi
  have hqi : IsIso (Work.Serre.ratHomologyMap (Work.Serre.mpathQ p) i) :=
    Work.Serre.E3aModel.serreE3aFibreAcyclic (Work.Serre.mpath p) B (Work.Serre.mpathQ p) (p e₀) N hq hB hfib h0 i hi
  have hfst : IsIso (Work.Serre.ratHomologyMap (Work.Serre.mpathFst p) i) :=
    Work.Serre.mpathFst_ratHomologyIso p i
  have hhom : (p.comp (Work.Serre.mpathFst p)).Homotopic (Work.Serre.mpathQ p) :=
    Work.Serre.mpath_homotopic p
  have hcomp : Work.Serre.ratHomologyMap (p.comp (Work.Serre.mpathFst p)) i
      = Work.Serre.ratHomologyMap (Work.Serre.mpathFst p) i ≫ Work.Serre.ratHomologyMap p i :=
    Work.Serre.ratHomologyMap_comp (Work.Serre.mpathFst p) p i
  have heq : Work.Serre.ratHomologyMap (p.comp (Work.Serre.mpathFst p)) i
      = Work.Serre.ratHomologyMap (Work.Serre.mpathQ p) i :=
    Work.Serre.ratHomologyMap_eq_of_homotopic hhom.some i
  haveI := hfst
  have h2 : IsIso (Work.Serre.ratHomologyMap (Work.Serre.mpathFst p) i ≫ Work.Serre.ratHomologyMap p i) := by
    rw [← hcomp, heq]; exact hqi
  exact IsIso.of_isIso_comp_left (Work.Serre.ratHomologyMap (Work.Serre.mpathFst p) i)
    (Work.Serre.ratHomologyMap p i)

/-! ## Elementary transport lemmas -/

/-- The image of a subsingleton under a surjective map is a subsingleton. -/
theorem subsingleton_of_surjective_aux {α β : Type*} (hα : Subsingleton α) (f : α → β)
    (hf : Function.Surjective f) : Subsingleton β :=
  ⟨fun a b => by
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    rw [hα.elim x y]⟩

/-- Finiteness of `π_k` transports forward along a `π_k`-bijection. -/
theorem fintype_of_bijective_piMapN {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (k : ℕ) (x : X)
    (hbij : Function.Bijective (Work.Serre.piMapN f k x))
    (h : Nonempty (Fintype (HomotopyGroup (Fin k) X x))) :
    Nonempty (Fintype (HomotopyGroup (Fin k) Y (f x))) :=
  ⟨by letI := h.some; exact Fintype.ofEquiv _ (Equiv.ofBijective _ hbij)⟩

/-- Finiteness of `π_{k+1}` transports backward along a bijective `πmap`. -/
theorem fintype_of_bijective_pimap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (k : ℕ) (x : X)
    (hbij : Function.Bijective (Work.StemsB.πmap f k x))
    (h : Nonempty (Fintype (HomotopyGroup (Fin (k + 1)) Y (f x)))) :
    Nonempty (Fintype (HomotopyGroup (Fin (k + 1)) X x)) :=
  ⟨by letI := h.some; exact Fintype.ofEquiv _ (Equiv.ofBijective (⇑(Work.StemsB.πmap f k x)) hbij).symm⟩

/-- A morphism of rational modules whose source and target are subsingletons is an isomorphism. -/
theorem isIso_of_subsingleton_module {M N : ModuleCat ℚ} (hM : Subsingleton (↥M))
    (hN : Subsingleton (↥N)) (f : M ⟶ N) : IsIso f := by
  haveI := hM
  haveI := hN
  refine IsIso.mk ⟨(0 : N ⟶ M), ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext x
    exact Subsingleton.elim _ _
  · apply ModuleCat.hom_ext
    ext y
    exact Subsingleton.elim _ _

/-! ## The range form of the theorem -/

/-- **Core induction.**  Let `W` be `1`-connected, with `π_i(W)` finite for `2 ≤ i ≤ n` and
`π_i(W) = 0` for `n < i ≤ N`.  Then `H_t(W;ℚ) = 0` for `0 < t ≤ N - 2n - 1`.

Proved by induction on `n`.  The step replaces `W` by its `n`-truncation `Q` (induction
hypothesis) and its homotopy fibre `Z`, which is a `K(π_{n+1}(W), n+1)`-model in the range and
hence rationally acyclic by `RangeEMVanAllFin`; the general mapping theorem
(`isRatHomologyIso_of_ratAcyclicBelow_homotopyFibre`) then transfers the vanishing from `Q` to
`W`. -/
theorem ratVanishing_of_finite_homotopy_aux (hEM : Work.Serre.RangeEMVanAllFin) :
    ∀ (n : ℕ) (N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W),
      1 ≤ n → n + 2 ≤ N →
      Subsingleton (HomotopyGroup (Fin 0) W w₀) →
      Subsingleton (HomotopyGroup (Fin 1) W w₀) →
      (∀ i : ℕ, 2 ≤ i → i ≤ n → Nonempty (Fintype (HomotopyGroup (Fin i) W w₀))) →
      (∀ i : ℕ, n < i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀)) →
      ∀ t : ℕ, 0 < t → t ≤ N - 2 * n - 1 → IsZero (Work.Serre.ratH (TopCat.of W) t) := by
  intro n
  induction n with
  | zero =>
    intro N W _ w₀ hn1
    exact absurd hn1 (by omega)
  | succ n ih =>
    intro N W _ w₀ hn1 hnN h0 h1 hfin hzero
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- ## base case `n + 1 = 1`: `W` is `N`-connected
      subst hn
      intro t ht htN
      have hall : ∀ i : ℕ, i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀) := by
        intro i hi
        cases i with
        | zero => exact h0
        | succ k =>
          cases k with
          | zero => exact h1
          | succ k => exact hzero (k + 2) (by omega) hi
      exact (Work.Serre.serreE0Range W w₀ N hall) t ht (by omega)
    · -- ## inductive step
      -- the `n`-truncation `Q` of `W`
      obtain ⟨Q, tQ, g, hg1, hg2⟩ := Work.Serre.serrePostnikovTower n N W w₀ (by omega)
      letI : TopologicalSpace Q := tQ
      have hpi0Q : Subsingleton (HomotopyGroup (Fin 0) Q (g w₀)) :=
        subsingleton_of_surjective_aux h0 (Work.Serre.piMapN g 0 w₀) (hg1 0 (by omega)).2
      have hpi1Q : Subsingleton (HomotopyGroup (Fin 1) Q (g w₀)) :=
        subsingleton_of_surjective_aux h1 (Work.Serre.piMapN g 1 w₀) (hg1 1 (by omega)).2
      have hfinQ : ∀ i : ℕ, 2 ≤ i → i ≤ n →
          Nonempty (Fintype (HomotopyGroup (Fin i) Q (g w₀))) := by
        intro i hi2 hin
        exact fintype_of_bijective_piMapN g i w₀ (hg1 i hin) (hfin i hi2 (by omega))
      have hzeroQ : ∀ i : ℕ, n < i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) Q (g w₀)) :=
        fun i hi hiN => hg2 i hi hiN (g w₀)
      have hQ := ih N Q (g w₀) (by omega : 1 ≤ n) (by omega : n + 2 ≤ N)
        hpi0Q hpi1Q hfinQ hzeroQ
      -- the homotopy fibre of the truncation, and its homotopy groups
      obtain ⟨hcov1, hcov2⟩ :=
        Work.Serre.serreConnectedCover n N (by omega : 1 ≤ n) (by omega : n < N) W w₀ Q g hg1 hg2
      -- `hEM` applied to the homotopy fibre
      have hZ0 : Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.homotopyFibre g w₀)
          (Work.RatHurewicz.homotopyFibreBasepoint g w₀)) := hcov1 0 (by omega)
      have hZcomm : ∀ a b : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre g w₀)
          (Work.RatHurewicz.homotopyFibreBasepoint g w₀), a * b = b * a := by
        haveI : Subsingleton (HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre g w₀)
            (Work.RatHurewicz.homotopyFibreBasepoint g w₀)) := hcov1 1 (by omega)
        exact fun a b => Subsingleton.elim _ _
      have hZvan : ∀ i : ℕ, 1 ≤ i → i ≤ N - 1 → i ≠ n + 1 →
          Subsingleton (HomotopyGroup (Fin i) (Work.RatHurewicz.homotopyFibre g w₀)
            (Work.RatHurewicz.homotopyFibreBasepoint g w₀)) := by
        intro i hi1 hiN hine
        by_cases hin : i ≤ n
        · exact hcov1 i hin
        · have hni : n < i := Nat.lt_of_not_le hin
          have hb := hcov2 i hni (by omega)
          have hidx : (i - 1) + 1 = i := Nat.sub_add_cancel hi1
          have hfz : (Work.RatHurewicz.homotopyFibreFst g w₀)
              (Work.RatHurewicz.homotopyFibreBasepoint g w₀) = w₀ := rfl
          have hcod : Subsingleton (HomotopyGroup (Fin ((i - 1) + 1)) W
              ((Work.RatHurewicz.homotopyFibreFst g w₀)
                (Work.RatHurewicz.homotopyFibreBasepoint g w₀))) := by
            rw [hidx, hfz]
            exact hzero i (by omega) (by omega)
          haveI := hcod
          have : Subsingleton (HomotopyGroup (Fin ((i - 1) + 1))
              (Work.RatHurewicz.homotopyFibre g w₀)
              (Work.RatHurewicz.homotopyFibreBasepoint g w₀)) :=
            ⟨fun a b => hb.1 (Subsingleton.elim
              ((Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g w₀) (i - 1)
                (Work.RatHurewicz.homotopyFibreBasepoint g w₀)) a)
              ((Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g w₀) (i - 1)
                (Work.RatHurewicz.homotopyFibreBasepoint g w₀)) b))⟩
          exact Work.Serre.serreAux_subsingleton_homotopyGroup_of_index_eq
            (x := Work.RatHurewicz.homotopyFibreBasepoint g w₀)
            (a := (i - 1) + 1) (b := i) hidx this
      have hZfin : Nonempty (Fintype (HomotopyGroup (Fin (n + 1))
          (Work.RatHurewicz.homotopyFibre g w₀)
          (Work.RatHurewicz.homotopyFibreBasepoint g w₀))) := by
        have hb : Function.Bijective (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g w₀) n
            (Work.RatHurewicz.homotopyFibreBasepoint g w₀)) :=
          Nat.succ_sub_one n ▸ hcov2 (n + 1) (by omega) (by omega)
        exact fintype_of_bijective_pimap (Work.RatHurewicz.homotopyFibreFst g w₀) n
          (Work.RatHurewicz.homotopyFibreBasepoint g w₀) hb
          (hfin (n + 1) (by omega) (by omega))
      have hZ := hEM n (N - 1) (Work.RatHurewicz.homotopyFibre g w₀)
        (Work.RatHurewicz.homotopyFibreBasepoint g w₀) hZ0 hZcomm hZvan hZfin
      have hZacyc : Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre g w₀)
          ((N - 1) - 1 - 2 * n) :=
        ⟨fun t ht htN => hZ t ht htN,
          Work.Serre.serreAux_isIso_toPoint_zero_of_subsingleton_pi_zero
            (Work.RatHurewicz.homotopyFibre g w₀)
            (Work.RatHurewicz.homotopyFibreBasepoint g w₀) hZ0⟩
      have hQpc : PathConnectedSpace Q :=
        Work.Serre.serreAux_pathConnected_of_subsingleton_pi_zero (g w₀) hpi0Q
      have hhom : ∀ i : ℕ, i < (N - 1) - 1 - 2 * n →
          IsIso (Work.Serre.ratHomologyMap g i) :=
        isRatHomologyIso_of_ratAcyclicBelow_homotopyFibre g w₀ ((N - 1) - 1 - 2 * n) hQpc hZacyc
      -- conclusion
      intro t ht htN
      have hQt : IsZero (Work.Serre.ratH (TopCat.of Q) t) := hQ t ht (by omega)
      haveI : IsIso (Work.Serre.ratHomologyMap g t) := hhom t (by omega)
      exact IsZero.of_iso hQt (asIso (Work.Serre.ratHomologyMap g t))

/-! ## The main theorem -/

/-- **A space with finitely many homotopy classes in every positive degree is rationally
acyclic in positive degrees.** -/
theorem isZero_ratH_of_finite_homotopy (X : Type) [TopologicalSpace X] (x₀ : X)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (h1 : Subsingleton (HomotopyGroup (Fin 1) X x₀))
    (hfin : ∀ i : ℕ, 2 ≤ i → Nonempty (Fintype (HomotopyGroup (Fin i) X x₀)))
    (hEM : Work.Serre.RangeEMVanAllFin)
    (j : ℕ) (hj : 0 < j) : IsZero (Work.Serre.ratH (TopCat.of X) j) := by
  haveI : Nonempty X := ⟨x₀⟩
  obtain ⟨P, tP, g, hg1, hg2, -⟩ :=
    Work.Serre.serrePostnikovTower_strong (3 * j + 5 - j) j (3 * j + 5) X rfl (by omega)
  letI : TopologicalSpace P := tP
  -- `H_j(X) ≅ H_j(P)` (`K2`)
  haveI hg : IsIso (Work.Serre.ratHomologyMap g j) :=
    Work.Serre.serreK2Proved X P g (j + 1) (fun i hi x => hg1 i (by omega) x) j (by omega)
  -- `P` satisfies the hypotheses of the induction
  have h0P : Subsingleton (HomotopyGroup (Fin 0) P (g x₀)) :=
    subsingleton_of_surjective_aux h0 (Work.Serre.piMapN g 0 x₀) (hg1 0 (by omega) x₀).2
  have h1P : Subsingleton (HomotopyGroup (Fin 1) P (g x₀)) :=
    subsingleton_of_surjective_aux h1 (Work.Serre.piMapN g 1 x₀) (hg1 1 (by omega) x₀).2
  have hfinP : ∀ i : ℕ, 2 ≤ i → i ≤ j →
      Nonempty (Fintype (HomotopyGroup (Fin i) P (g x₀))) := by
    intro i hi2 hij
    exact fintype_of_bijective_piMapN g i x₀ (hg1 i hij x₀) (hfin i hi2)
  have hzeroP : ∀ i : ℕ, j < i → i ≤ 3 * j + 5 → Subsingleton (HomotopyGroup (Fin i) P (g x₀)) :=
    fun i hi hiN => hg2 i hi hiN (g x₀)
  have hP : IsZero (Work.Serre.ratH (TopCat.of P) j) :=
    ratVanishing_of_finite_homotopy_aux hEM j (3 * j + 5) P (g x₀) (by omega) (by omega)
      h0P h1P hfinP hzeroP j hj (by omega)
  exact IsZero.of_iso hP (asIso (Work.Serre.ratHomologyMap g j))

theorem finiteHomotopyRatAcyclic (hEM : Work.Serre.RangeEMVanAllFin)
    (X : Type) [TopologicalSpace X] (x₀ : X)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (h1 : Subsingleton (HomotopyGroup (Fin 1) X x₀))
    (hfin : ∀ i : ℕ, 2 ≤ i → Nonempty (Fintype (HomotopyGroup (Fin i) X x₀))) :
    Work.Serre.RatAcyclic X := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Work.Serre.serreAux_isIso_toPoint_zero_of_subsingleton_pi_zero X x₀ h0
  · have hX : IsZero (Work.Serre.ratH (TopCat.of X) n) :=
      isZero_ratH_of_finite_homotopy X x₀ h0 h1 hfin hEM n hn
    have hP : IsZero (Work.Serre.ratH (TopCat.of PUnit) n) :=
      Work.Cohomology.homologyContractible_ring ℚ (X := TopCat.of PUnit) n hn
    exact isIso_of_subsingleton_module (Work.Serre.subsingleton_of_isZero hX)
      (Work.Serre.subsingleton_of_isZero hP) (Work.Serre.ratHomologyMap (Work.Serre.toPoint X) n)

end

end Work.Rat
