import Mathlib
import Submission.Work.Serre.serreS1OfRangeEMVan
import Submission.Work.Serre.RangeEMVanFinDefs

/-!
# The rational vanishing Hurewicz theorem, in **all** degrees, for finitely generated homotopy

`Work.Serre.serreS1OfRangeEMVan` proves the rational vanishing Hurewicz theorem `SerreS1` from the
mapping theorem `SerreE3a` and the range form of the acyclicity of the `K(A,·)` models, but its
statement carries the stable-range hypothesis `M ≤ 2k-2`, which is used **only** to guarantee that
the "first degree" `s` of the induction is `≥ 3`.

This file removes that hypothesis: the induction of `Work.Serre.serreAux_ind` is re-run with `3 ≤ s`
as an explicit hypothesis (so that the induction can start at any connectivity level), and with the
*finitely generated* input that makes the killed groups **finite** (a finitely generated torsion
group is finite), so that the finite-coefficient acyclicity result `RangeEMVanAllFin`
(`Work.Serre.serreRangeEMVanOneFin`) can be used in place of the open `RangeEMVanAll`.

The conclusion is what the sphere route consumes: for a simply connected space `X` with finitely
generated homotopy groups whose rational homology vanishes in degrees `≤ M`, every homotopy group
`π_j(X)`, `k ≤ j ≤ M`, is torsion — with `M` **arbitrary**.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Rat

noncomputable section

/-- **The double fibre of the cover map has a finite `π_{k+2}`.**  It is the `π_{k+2}` of the
homotopy fibre of `Fst : Z → Y`, which is a quotient of `π_{k+3}(Y)` (the connecting map of the pair
sequence is surjective because `π_{k+2}(Z) = 0`); a quotient of a finitely generated torsion group is
finite. -/
theorem fintype_relPi_of_fg {X A : Type} [TopologicalSpace X] [TopologicalSpace A]
    (i : C(A, X)) (a₀ : A) (k : ℕ)
    (hA2 : Subsingleton (HomotopyGroup (Fin (k + 2)) A a₀))
    (hfg : Group.FG (HomotopyGroup (Fin (k + 3)) X (i a₀)))
    (htors : ∀ β : HomotopyGroup (Fin (k + 3)) X (i a₀), ∃ K : ℕ, 0 < K ∧ β ^ K = 1) :
    Nonempty (Fintype (Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 2))) := by
  obtain ⟨del, d, h1, h2, h3, h4⟩ := Work.RatHurewicz.pair_les i a₀ (k + 1) (by omega)
  have hsurj : Function.Surjective d := by
    intro y
    have hy : (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) (k + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) y = 1 :=
      Work.Serre.serreAux_pair_e_eq_one i a₀ k hA2 y
    exact (h4 y).mp hy
  haveI hG : Group.FG (HomotopyGroup (Fin (k + 3)) X (i a₀)) := hfg
  have hcomm : ∀ g h : HomotopyGroup (Fin (k + 3)) X (i a₀), g * h = h * g := fun g h => mul_comm g h
  haveI hfin : Finite (HomotopyGroup (Fin (k + 3)) X (i a₀)) :=
    CommGroup.finite_of_fg_isMulTorsion _ (fun g => isOfFinOrder_iff_pow_eq_one.mpr (htors g))
  haveI : Finite (Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 2)) := Finite.of_surjective d hsurj
  exact ⟨Fintype.ofFinite _⟩

/-- A finitely generated homotopy group transports along an equality of the index. -/
theorem fg_of_index_eq {X : Type} [TopologicalSpace X] {x : X} {a b : ℕ}
    [Nonempty (Fin a)] [Nonempty (Fin b)] (h : a = b)
    (H : Group.FG (HomotopyGroup (Fin a) X x)) : Group.FG (HomotopyGroup (Fin b) X x) := by
  subst h; exact H

/-- **The main induction.**  `Y` is `(s-1)`-connected with finitely generated homotopy groups and
vanishing rational homology in degrees `s ≤ i ≤ M` (`3 ≤ s`); then `π_j(Y)` is torsion for
`s ≤ j ≤ M`.  The proof is that of `Work.Serre.serreAux_ind` with the stable-range hypothesis
replaced by `3 ≤ s` and the acyclicity input by the finite-coefficient `RangeEMVanAllFin`. -/
private theorem s1AuxFin (hE3a : Work.Serre.SerreE3a) (h : Work.Serre.RangeEMVanAllFin) :
    ∀ (d : ℕ), ∀ (s M : ℕ), M - s = d → 3 ≤ s → s ≤ M →
      ∀ (Y : Type) [TopologicalSpace Y] (y₀ : Y),
        (∀ i, i < s → Subsingleton (HomotopyGroup (Fin i) Y y₀)) →
        (∀ (a : ℕ) [Nonempty (Fin a)], a ≤ M → Group.FG (HomotopyGroup (Fin a) Y y₀)) →
        (∀ i, s ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of Y) i)) →
        (∀ m, s ≤ m + 1 → m + 1 ≤ M → Work.Serre.PiTorsion Y y₀ m) := by
  intro d
  induction d with
  | zero =>
    intro s M hMs hs3 hsM Y _ y₀ hconn hfg hhom m hm1 hm2
    have hMs0 : M = s := le_antisymm (Nat.sub_eq_zero_iff_le.mp hMs) hsM
    have hm2' : m + 1 ≤ s := by rw [hMs0] at hm2; exact hm2
    have hs' : s = m + 1 := le_antisymm hm1 hm2'
    subst hs'
    exact Work.Serre.serreAuxTorsionFirstDegree (m := m) (by omega) y₀ (fun i hi => hconn i hi)
      (Work.Serre.subsingleton_of_isZero (hhom (m + 1) le_rfl hm2))
  | succ d ih =>
    intro s M hMs hs3 hsM Y _ y₀ hconn hfg hhom m hm1 hm2
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 3 := ⟨s - 3, by omega⟩
    have htors : ∀ β : HomotopyGroup (Fin (k + 3)) Y y₀, ∃ K : ℕ, 0 < K ∧ β ^ K = 1 :=
      Work.Serre.serreAuxTorsionFirstDegree (m := k + 2) (by omega) y₀ (fun i hi => hconn i (by omega))
        (Work.Serre.subsingleton_of_isZero (hhom (k + 3) (by omega) (by omega)))
    set N' : ℕ := M + 2 * (k + 3) + 4 with hN'def
    obtain ⟨P, tP, g, hg1, hg2⟩ := Work.Serre.serrePostnikovTower (k + 3) N' Y y₀ (by omega)
    letI := tP
    let Z : Type := Work.RatHurewicz.homotopyFibre g y₀
    let z₀ : Z := Work.RatHurewicz.homotopyFibreBasepoint g y₀
    let Fst : C(Z, Y) := Work.RatHurewicz.homotopyFibreFst g y₀
    obtain ⟨hcov1, hcov2⟩ :=
      Work.Serre.serreConnectedCover (k + 3) N' (by omega) (by omega) Y y₀ P g hg1 hg2
    let F : Type := Work.RatHurewicz.homotopyFibre Fst z₀
    let f₀ : F := Work.RatHurewicz.homotopyFibreBasepoint Fst z₀
    have hF_low : ∀ j, 1 ≤ j → j ≤ k + 1 → Subsingleton (HomotopyGroup (Fin j) F f₀) := by
      intro j hj1 hjk
      by_cases hj : j = 1
      · subst hj
        exact Work.Serre.serreAux_pi_one_homotopyFibre_subsingleton Fst z₀
          (hcov1 1 (by omega)) (hconn 2 (by omega))
      · have hZ : Subsingleton (HomotopyGroup (Fin ((j - 2) + 2)) Z z₀) :=
          Work.Serre.serreAux_subsingleton_homotopyGroup_of_index_eq (x := z₀) (a := j) (b := (j - 2) + 2)
            (by omega) (hcov1 j (by omega))
        have hY : Subsingleton (HomotopyGroup (Fin (((j - 2) + 2) + 1)) Y y₀) :=
          Work.Serre.serreAux_subsingleton_homotopyGroup_of_index_eq (x := y₀) (a := j + 1)
            (b := ((j - 2) + 2) + 1) (by omega) (hconn (j + 1) (by omega))
        have hres : Subsingleton (Work.RatHurewicz.RelHomotopyGroup Fst z₀ ((j - 2) + 2)) :=
          Work.Serre.serreAux_relPi_subsingleton_of_subsingleton Fst z₀ (j - 2) hZ hY
        exact Work.Serre.serreAux_subsingleton_homotopyGroup_of_index_eq (x := f₀) (a := (j - 2) + 2)
          (b := j) (by omega) hres
    have hF_high : ∀ j, k + 3 ≤ j → j + 2 ≤ N' → Subsingleton (HomotopyGroup (Fin j) F f₀) := by
      intro j hj hjN
      have hinj : Function.Injective (Work.StemsB.πmap Fst ((j - 2) + 1) z₀) := by
        by_cases hj' : j = k + 3
        · have hZ := Work.Serre.serreAux_subsingleton_homotopyGroup_of_index_eq (x := z₀) (a := k + 3)
            (b := ((j - 2) + 1) + 1) (by omega) (hcov1 (k + 3) le_rfl)
          haveI := hZ
          exact fun a b _ => Subsingleton.elim a b
        · exact (by omega : j - 1 = (j - 2) + 1) ▸ (hcov2 j (by omega) (by omega)).1
      have hsurj : Function.Surjective (Work.StemsB.πmap Fst ((j - 2) + 2) z₀) :=
        (by omega : (j + 1) - 1 = (j - 2) + 2) ▸ (hcov2 (j + 1) (by omega) (by omega)).2
      have hres : Subsingleton (Work.RatHurewicz.RelHomotopyGroup Fst z₀ ((j - 2) + 2)) :=
        Work.Serre.serreAux_relPi_subsingleton_of_injective_surjective Fst z₀ (j - 2) (by omega) hinj hsurj
      exact Work.Serre.serreAux_subsingleton_homotopyGroup_of_index_eq (x := f₀) (a := (j - 2) + 2)
        (b := j) (by omega) hres
    have hF_pi0 : Subsingleton (HomotopyGroup (Fin 0) F f₀) := by
      have hApath : ∀ a : Z, Joined z₀ a :=
        (Work.Serre.serreAux_pathConnected_of_subsingleton_pi_zero z₀ (hcov1 0 (by omega))).joined z₀
      have hfib : Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.fibreOf Fst z₀)
          (Work.RatHurewicz.fibreOfPt Fst z₀)) :=
        Work.Serre.serreAux_subsingleton_pi_zero_fibreOf Fst z₀
          (Work.Serre.subsingleton_pi0_loopSpace_of_pi1 y₀ (hconn 1 (by omega)))
      exact Work.Serre.subsingleton_pi0_homotopyFibre Fst z₀ hApath hfib
    have hvan_van : ∀ i : ℕ, 1 ≤ i → i ≤ N' - 2 → i ≠ k + 1 + 1 →
        Subsingleton (HomotopyGroup (Fin i) F f₀) := by
      intro i hi1 hiN hine
      by_cases hlow : i ≤ k + 1
      · exact hF_low i hi1 hlow
      · exact hF_high i (by omega) (by omega)
    -- finiteness of `π_{k+2}(F)` from the f.g. + torsion input
    have hfinF : Nonempty (Fintype (HomotopyGroup (Fin ((k + 1) + 1)) F f₀)) := by
      have hA2 : Subsingleton (HomotopyGroup (Fin (k + 2)) Z z₀) :=
        hcov1 (k + 2) (by omega)
      have hfgY : Group.FG (HomotopyGroup (Fin (k + 3)) Y y₀) := hfg (k + 3) (by omega)
      exact fintype_relPi_of_fg Fst z₀ k hA2 hfgY
        (fun β => htors β)
    have hF_comm : ∀ a b : HomotopyGroup (Fin 1) F f₀, a * b = b * a :=
      Work.Serre.serreAux_pi_one_comm Fst z₀ (hcov1 1 (by omega))
    have hvanF' := h (k + 1) (N' - 2) F f₀ hF_pi0 hF_comm hvan_van hfinF
    have hvanF : ∀ t : ℕ, 0 < t → t ≤ M + 2 → IsZero (Work.Serre.ratH (TopCat.of F) t) := by
      intro t ht0 htM
      refine hvanF' t ht0 ?_
      have hle : (N' - 2) - 1 - 2 * (k + 1) = M + 5 := by omega
      omega
    have hiso : ∀ i, i < M + 2 → IsIso (Work.Serre.ratHomologyMap Fst i) := by
      refine hE3a Z Y Fst z₀ (M + 2)
        (Work.RatHurewicz.isSerreFibration_homotopyFibreFst g y₀)
        (Work.Serre.serreAux_pathConnected_of_subsingleton_pi_zero y₀ (hconn 0 (by omega)))
        ⟨hvanF, ?_⟩
      exact Work.Serre.serreAux_isIso_toPoint_zero_of_subsingleton_pi_zero F f₀ hF_pi0
    have hhomZ : ∀ i, k + 4 ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of Z) i) := by
      intro i hi1 hi2
      haveI : IsIso (Work.Serre.ratHomologyMap Fst i) := hiso i (by omega)
      exact IsZero.of_iso (hhom i (by omega) hi2) (asIso (Work.Serre.ratHomologyMap Fst i))
    -- the finitely generated homotopy groups of the cover
    have hfgZ : ∀ (a : ℕ) [Nonempty (Fin a)], a ≤ M → Group.FG (HomotopyGroup (Fin a) Z z₀) := by
      intro a _ haM
      by_cases his : a ≤ k + 3
      · haveI : Subsingleton (HomotopyGroup (Fin a) Z z₀) := hcov1 a his
        haveI : Finite (HomotopyGroup (Fin a) Z z₀) := Finite.of_subsingleton
        exact Group.fg_iff_monoid_fg.mpr Monoid.fg_of_finite
      · have hidx : (a - 1) + 1 = a := by omega
        haveI : Nonempty (Fin ((a - 1) + 1)) := ⟨⟨0, Nat.succ_pos _⟩⟩
        have hbij := hcov2 a (by omega) (by omega)
        haveI : Group.FG (HomotopyGroup (Fin ((a - 1) + 1)) Y y₀) := hfg ((a - 1) + 1) (by omega)
        have hZfg : Group.FG (HomotopyGroup (Fin ((a - 1) + 1)) Z z₀) := by
          let e : HomotopyGroup (Fin ((a - 1) + 1)) Z z₀ ≃*
              HomotopyGroup (Fin ((a - 1) + 1)) Y y₀ := MulEquiv.ofBijective _ hbij
          exact Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
        exact fg_of_index_eq hidx hZfg
    have hIH := ih (k + 4) M (by omega) (by omega) (by omega) Z z₀
      (fun i hi => hcov1 i (by omega)) hfgZ hhomZ
    by_cases hm : m + 1 = k + 3
    · exact Work.Serre.serreAux_piTorsion_of_index_eq y₀ (by omega : k + 2 = m) htors
    · have hsurj : Function.Surjective (Work.StemsB.πmap Fst m z₀) :=
        (by omega : (m + 1) - 1 = m) ▸ (hcov2 (m + 1) (by omega) (by omega)).2
      exact Work.Serre.serreAux_piTorsion_of_surjective_hom (Work.StemsB.πmap Fst m z₀) hsurj
        (hIH m (by omega) hm2)

/-- **The rational vanishing Hurewicz theorem in all degrees, for finitely generated homotopy.**
Let `X` be `(k-1)`-connected (`k ≥ 3`) with finitely generated homotopy groups, and suppose
`H̃_i(X;ℚ) = 0` for `k ≤ i ≤ M`.  Then `π_j(X)` is torsion for `k ≤ j ≤ M` — with `M` arbitrary. -/
theorem piTorsion_of_ratH_vanishing_full (hE3a : Work.Serre.SerreE3a)
    (h : Work.Serre.RangeEMVanAllFin)
    (k : ℕ) (hk : 3 ≤ k) (X : Type) [TopologicalSpace X] (x₀ : X)
    (M : ℕ) (hconn : ∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀))
    (hfg : ∀ (a : ℕ) [Nonempty (Fin a)], a ≤ M → Group.FG (HomotopyGroup (Fin a) X x₀))
    (hhom : ∀ i, k ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of X) i)) :
    ∀ j : ℕ, k ≤ j → j ≤ M → Work.Serre.PiTorsion X x₀ (j - 1) := by
  intro j hkj hjM
  exact s1AuxFin hE3a h (M - k) k M rfl hk (by omega) X x₀ hconn hfg hhom (j - 1)
    (by omega) (by omega)

end

end Work.Rat
