/-
  WilE5 — `Cells/khovCount`: Khovanskii's polynomial bound on the number of *consistent sign
  conditions* (cells) of an EA semi-Pfaffian set, derived from the frozen `E2_components`
  hypothesis (a polynomial bound on the number of connected components of a semi-Pfaffian set
  of bounded format).

  The argument is Gabrielov–Vorobjov (*Complexity of stratifications*, Prop. 2).  Let `f_i`
  (`i : Fin N`) be the atoms of `X` and pick a point `z_σ` in every sign cell `σ`.  Choose
  `ε > 0` so small that `|f_i (z_σ)| > ε` whenever `f_i (z_σ) ≠ 0` (possible: finitely many
  conditions).  Put `g_i := (f_i + ε)² (f_i - ε)²` and let `Z := {x ∈ cubeC : ∀ i, g_i x > 0}`,
  a semi-Pfaffian set of the *same format* as `X` and degree `≤ 4 * X.deg`.

  Every chosen point `z_σ` lies in `Z`.  Two points from different sign cells lie in different
  connected components of `Z`: if they were in one component, the intermediate value theorem on
  the connected component produces a point with `f_i = ε` or `f_i = -ε`, where `g_i = 0`.

  Hence the number of cells is bounded by the number of components of `Z`, which `E2_components`
  bounds by a polynomial in `Z.deg ≤ 4 * X.deg`.

  The four ingredients `khovEps` (finiteness of the threshold), `khovAtomEval`/`khovAtomPos`
  (evaluation of the perturbed atoms) and `khovDegEq`/`khovPosDeg` (degree bookkeeping) are proved
  in the sibling modules of this directory.
-/
import Mathlib
import Submission.Work.WilE5.Cells
import Submission.Work.WilE5.Basic
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE5.Cells.khovEps
import Submission.Work.WilE5.Cells.khovAtomEval
import Submission.Work.WilE5.Cells.khovAtomPos
import Submission.Work.WilE5.Cells.khovDegEq
import Submission.Work.WilE5.Cells.khovPosDeg

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE5.Cells
open WilkiesDesign WilkiesDesign.E

/-! ## §0. Definitions -/

/-- A point chosen in each nonempty sign cell of `X` (and `0` in the empty ones). -/
def khovCellPt {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign) : Fin k → ℝ :=
  if h : (cellSemiPf X σ).set.Nonempty then h.choose else 0

/-- The Khovanskii perturbation `(f + ε)² (f - ε)²` of an atom. -/
def khovAt {k r : ℕ} (f : EAPoly k r) (ε : ℝ) : EAPoly k r :=
  (f + MvPolynomial.C ε) ^ 2 * (f - MvPolynomial.C ε) ^ 2

/-- The list of perturbed atoms. -/
def khovAtoms {k : ℕ} (X : SemiPf k) (ε : ℝ) : List (EAPoly k X.r) :=
  (atomsOf X).map fun f => khovAt f ε

/-- The auxiliary semi-Pfaffian set whose positive conditions are the perturbed atoms. -/
def khovSet {k : ℕ} (X : SemiPf k) (ε : ℝ) : SemiPf k :=
  ⟨X.r, X.c, [⟨[], khovAtoms X ε⟩]⟩

/-! ## §1. Elementary helpers -/

/-- `Polynomial.eval` at natural numbers is monotone (all coefficients are nonnegative). -/
theorem khovEval_mono {p : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum fun n _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

/-- `eaEval` of a fixed EA-polynomial is continuous. -/
theorem khovEaEval_continuous {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    Continuous fun x : Fin k → ℝ => eaEval c Q x :=
  continuous_iff_continuousAt.mpr fun x => (Calc.hasFDerivAt_eaEval c Q x).continuousAt

/-! ## §2. The sign cells -/

theorem khovMemCell {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    (x : Fin k → ℝ) :
    x ∈ (cellSemiPf X σ).set ↔ x ∈ cubeC k ∧ (cell X σ).holds X.c x := by
  unfold cellSemiPf SemiPf.set
  simp only [Set.mem_ofPred_eq, List.mem_singleton]
  constructor
  · rintro ⟨h1, B, hB, h2⟩
    subst hB
    exact ⟨h1, h2⟩
  · exact fun h => ⟨h.1, cell X σ, rfl, h.2⟩

theorem khovCell_zero {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    {x : Fin k → ℝ} (hx : x ∈ (cellSemiPf X σ).set) {i : Fin (atomsOf X).length}
    (hi : σ i = Sign.zero) : eaEval X.c ((atomsOf X).get i) x = 0 := by
  obtain ⟨-, hholds⟩ := (khovMemCell X σ x).mp hx
  simp only [cell, Basic.holds, cellEqs] at hholds
  refine hholds.1 ((atomsOf X).get i) ?_
  rw [List.mem_map]
  refine ⟨i, ?_, rfl⟩
  rw [Finset.mem_toList, Finset.mem_filter]
  exact ⟨Finset.mem_univ i, by simp [hi]⟩

theorem khovCell_pos {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    {x : Fin k → ℝ} (hx : x ∈ (cellSemiPf X σ).set) {i : Fin (atomsOf X).length}
    (hi : σ i = Sign.pos) : 0 < eaEval X.c ((atomsOf X).get i) x := by
  obtain ⟨-, hholds⟩ := (khovMemCell X σ x).mp hx
  simp only [cell, Basic.holds, cellPos] at hholds
  refine hholds.2 ((atomsOf X).get i) ?_
  rw [List.mem_map]
  refine ⟨i, ?_, by simp [hi]⟩
  rw [Finset.mem_toList, Finset.mem_filter]
  exact ⟨Finset.mem_univ i, by simp [hi]⟩

theorem khovCell_neg {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    {x : Fin k → ℝ} (hx : x ∈ (cellSemiPf X σ).set) {i : Fin (atomsOf X).length}
    (hi : σ i = Sign.neg) : eaEval X.c ((atomsOf X).get i) x < 0 := by
  obtain ⟨-, hholds⟩ := (khovMemCell X σ x).mp hx
  simp only [cell, Basic.holds, cellPos] at hholds
  have hpos := hholds.2 (-((atomsOf X).get i)) ?_
  · rw [eaEval_neg] at hpos
    linarith
  · rw [List.mem_map]
    refine ⟨i, ?_, by simp [hi]⟩
    rw [Finset.mem_toList, Finset.mem_filter]
    exact ⟨Finset.mem_univ i, by simp [hi]⟩

theorem khovCellPt_mem {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    (h : (cellSemiPf X σ).set.Nonempty) : khovCellPt X σ ∈ (cellSemiPf X σ).set := by
  rw [khovCellPt, dif_pos h]
  exact h.choose_spec

/-- The sign data of one atom at one point. -/
def KhovSignData (u : Sign) (a ε : ℝ) : Prop :=
  (u = Sign.zero ∧ a = 0) ∨ (u = Sign.pos ∧ ε < a) ∨ (u = Sign.neg ∧ a < -ε)

/-- Assembly of the sign data from the three possible signs of the point. -/
theorem KhovSignData.of_sign {u : Sign} {a ε : ℝ} (hz : u = Sign.zero → a = 0)
    (hp : u = Sign.pos → ε < a) (hn : u = Sign.neg → a < -ε) : KhovSignData u a ε := by
  rcases u with _ | _ | _
  · exact Or.inl ⟨rfl, hz rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, hp rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, hn rfl⟩)

/-- Two atoms with different sign data are separated by one of `± ε`. -/
theorem khovSignData_cross {u v : Sign} (h : u ≠ v) {a b ε : ℝ} (hε : 0 < ε)
    (ha : KhovSignData u a ε) (hb : KhovSignData v b ε) :
    (a ≤ ε ∧ ε ≤ b) ∨ (b ≤ ε ∧ ε ≤ a) ∨ (a ≤ -ε ∧ -ε ≤ b) ∨ (b ≤ -ε ∧ -ε ≤ a) := by
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩
  · rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
    · exact absurd rfl h
    · exact Or.inl ⟨le_of_lt hε, le_of_lt hb⟩
    · exact Or.inr (Or.inr (Or.inr ⟨le_of_lt hb, by linarith⟩))
  · rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
    · exact Or.inr (Or.inl ⟨le_of_lt hε, le_of_lt ha⟩)
    · exact absurd rfl h
    · exact Or.inr (Or.inl ⟨by linarith, le_of_lt ha⟩)
  · rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
    · exact Or.inr (Or.inr (Or.inl ⟨le_of_lt ha, by linarith⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨le_of_lt ha, by linarith⟩))
    · exact absurd rfl h

/-! ## §3. The auxiliary set -/

theorem khovAt_pos {k r : ℕ} (c : EAChain k r) (ε : ℝ) (f : EAPoly k r) (x : Fin k → ℝ) :
    0 < eaEval c (khovAt f ε) x ↔ eaEval c f x ≠ ε ∧ eaEval c f x ≠ -ε :=
  khovAtomPos c ε f x

theorem khovSet_mem {k : ℕ} (X : SemiPf k) (ε : ℝ) (x : Fin k → ℝ) :
    x ∈ (khovSet X ε).set ↔ x ∈ cubeC k ∧ ∀ g ∈ khovAtoms X ε, 0 < eaEval X.c g x := by
  unfold khovSet SemiPf.set
  simp only [Set.mem_ofPred_eq, List.mem_singleton]
  constructor
  · rintro ⟨h1, B, hB, h2⟩
    subst hB
    refine ⟨h1, ?_⟩
    simpa [Basic.holds] using h2.2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ⟨[], khovAtoms X ε⟩, rfl, by simpa [Basic.holds] using h2⟩

theorem khovSet_deg_le {k : ℕ} (X : SemiPf k) (ε : ℝ) :
    (khovSet X ε).deg ≤ 4 * X.deg := by
  have h1 : (khovSet X ε).deg = ((khovAtoms X ε).map atomDeg).sum := by
    simp [khovSet, SemiPf.deg, Basic.deg]
  rw [h1]
  have h := khovPosDeg X ε
  rw [khovDegEq X] at h
  simpa [khovAtoms, khovAt, List.map_map, Function.comp_def] using h

/-! ## §4. The counting theorem -/

theorem khovCount
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (kk : ℕ) (X : WilkiesDesign.E.SemiPf kk), X.fmt ≤ F →
      ∃ s : Finset (Fin kk → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y)
    (F : ℕ) :
    ∃ b : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      (Work.WilE5.goodCells X).length ≤ b.eval X.deg := by
  classical
  obtain ⟨p, hp⟩ := hE2 F
  refine ⟨p.comp (Polynomial.C 4 * Polynomial.X + Polynomial.C 1), ?_⟩
  intro k X hF
  -- the threshold ε, small enough at all chosen cell points
  obtain ⟨ε, hεpos, hε⟩ := khovEps
    (fun q : Fin (atomsOf X).length × (Fin (atomsOf X).length → Sign) =>
      eaEval X.c ((atomsOf X).get q.1) (khovCellPt X q.2))
  have hmem_good : ∀ σ : Fin (atomsOf X).length → Sign, σ ∈ goodCells X ↔
      (cellSemiPf X σ).set.Nonempty ∧ (cellSemiPf X σ).set ⊆ X.set := by
    intro σ
    rw [goodCells, allSigns, List.mem_filter]
    constructor
    · intro h; exact of_decide_eq_true h.2
    · intro h; exact ⟨by simp, by rw [decide_eq_true_eq]; exact h⟩
  -- the sign data of a good cell at its chosen point
  have hsignData : ∀ (σ : Fin (atomsOf X).length → Sign), σ ∈ goodCells X →
      ∀ i : Fin (atomsOf X).length,
      KhovSignData (σ i) (eaEval X.c ((atomsOf X).get i) (khovCellPt X σ)) ε := by
    intro σ hσ i
    have hnon := (hmem_good σ).mp hσ |>.1
    have hpt := khovCellPt_mem X σ hnon
    refine KhovSignData.of_sign (fun hz => khovCell_zero X σ hpt hz) (fun hp => ?_)
      (fun hn => ?_)
    · have hpos := khovCell_pos X σ hpt hp
      have hlt := hε ⟨i, σ⟩ (ne_of_gt hpos)
      rwa [abs_of_pos hpos] at hlt
    · have hneg := khovCell_neg X σ hpt hn
      have hlt := hε ⟨i, σ⟩ (ne_of_lt hneg)
      rw [abs_of_neg hneg] at hlt
      linarith
  -- every chosen point of a good cell lies in the auxiliary set
  have hpt_mem : ∀ σ ∈ goodCells X, khovCellPt X σ ∈ (khovSet X ε).set := by
    intro σ hσ
    have hnon := (hmem_good σ).mp hσ |>.1
    have hpt := khovCellPt_mem X σ hnon
    have hcube : khovCellPt X σ ∈ cubeC k := ((khovMemCell X σ (khovCellPt X σ)).mp hpt).1
    rw [khovSet_mem]
    refine ⟨hcube, ?_⟩
    intro g hg
    rw [khovAtoms, List.mem_map] at hg
    obtain ⟨f, hf, hfg⟩ := hg
    subst hfg
    rw [List.mem_iff_get] at hf
    obtain ⟨i, hi⟩ := hf
    subst hi
    rw [khovAt_pos]
    rcases hsignData σ hσ i with ⟨-, hz⟩ | ⟨-, hz⟩ | ⟨-, hz⟩
    · exact ⟨fun h => by linarith, fun h => by linarith⟩
    · exact ⟨fun h => by linarith, fun h => by linarith⟩
    · exact ⟨fun h => by linarith, fun h => by linarith⟩
  -- distinct good cells have chosen points in different components
  have hsep : ∀ σ ∈ goodCells X, ∀ τ ∈ goodCells X, σ ≠ τ →
      connectedComponentIn (khovSet X ε).set (khovCellPt X σ) ≠
        connectedComponentIn (khovSet X ε).set (khovCellPt X τ) := by
    intro σ hσ τ hτ hne heq
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hne (funext hc)
    have hσmem := hpt_mem σ hσ
    have hτmem := hpt_mem τ hτ
    have hApre : IsPreconnected
        (connectedComponentIn (khovSet X ε).set (khovCellPt X σ)) :=
      isPreconnected_connectedComponentIn
    have hτA : khovCellPt X τ ∈ connectedComponentIn (khovSet X ε).set (khovCellPt X σ) := by
      rw [heq]
      exact mem_connectedComponentIn hτmem
    have hcont : ContinuousOn (fun z : Fin k → ℝ => eaEval X.c ((atomsOf X).get i) z)
        (connectedComponentIn (khovSet X ε).set (khovCellPt X σ)) :=
      (khovEaEval_continuous X.c ((atomsOf X).get i)).continuousOn
    have key : ∀ z ∈ connectedComponentIn (khovSet X ε).set (khovCellPt X σ),
        eaEval X.c ((atomsOf X).get i) z ≠ ε ∧
          eaEval X.c ((atomsOf X).get i) z ≠ -ε := by
      intro z hzA
      have hzY : z ∈ (khovSet X ε).set := connectedComponentIn_subset _ _ hzA
      have hgmem : khovAt ((atomsOf X).get i) ε ∈ khovAtoms X ε := by
        rw [khovAtoms, List.mem_map]
        exact ⟨_, List.get_mem _ _, rfl⟩
      have hpos := ((khovSet_mem X ε z).mp hzY).2 _ hgmem
      rwa [khovAt_pos] at hpos
    have reach : ∀ w : ℝ,
        ((eaEval X.c ((atomsOf X).get i) (khovCellPt X σ) ≤ w ∧
            w ≤ eaEval X.c ((atomsOf X).get i) (khovCellPt X τ)) ∨
          (eaEval X.c ((atomsOf X).get i) (khovCellPt X τ) ≤ w ∧
            w ≤ eaEval X.c ((atomsOf X).get i) (khovCellPt X σ))) →
        ∃ z ∈ connectedComponentIn (khovSet X ε).set (khovCellPt X σ),
          eaEval X.c ((atomsOf X).get i) z = w := by
      intro w hw
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (Set.mem_image _ _ _).mp
          (hApre.intermediate_value (mem_connectedComponentIn hσmem) hτA hcont ⟨h1, h2⟩)
      · exact (Set.mem_image _ _ _).mp
          (hApre.intermediate_value hτA (mem_connectedComponentIn hσmem) hcont ⟨h1, h2⟩)
    have hcross := khovSignData_cross hi hεpos (hsignData σ hσ i) (hsignData τ hτ i)
    rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨z, hzA, hz⟩ := reach ε (Or.inl ⟨h1, h2⟩)
      exact (key z hzA).1 hz
    · obtain ⟨z, hzA, hz⟩ := reach ε (Or.inr ⟨h1, h2⟩)
      exact (key z hzA).1 hz
    · obtain ⟨z, hzA, hz⟩ := reach (-ε) (Or.inl ⟨h1, h2⟩)
      exact (key z hzA).2 hz
    · obtain ⟨z, hzA, hz⟩ := reach (-ε) (Or.inr ⟨h1, h2⟩)
      exact (key z hzA).2 hz
  -- apply E2 to the auxiliary set
  have hYfmt : (khovSet X ε).fmt ≤ F := hF
  obtain ⟨s, hscard, hssub, hscov⟩ := hp k (khovSet X ε) hYfmt
  have hex : ∀ σ ∈ (goodCells X).toFinset, ∃ y ∈ s,
      connectedComponentIn (khovSet X ε).set (khovCellPt X σ) =
        connectedComponentIn (khovSet X ε).set y := by
    intro σ hσ
    exact hscov (khovCellPt X σ) (hpt_mem σ (List.mem_toFinset.mp hσ))
  have hex2 : ∀ σ : Fin (atomsOf X).length → Sign, ∃ y : Fin k → ℝ,
      (σ ∈ (goodCells X).toFinset → y ∈ s ∧
        connectedComponentIn (khovSet X ε).set (khovCellPt X σ) =
          connectedComponentIn (khovSet X ε).set y) := by
    intro σ
    by_cases h : σ ∈ (goodCells X).toFinset
    · obtain ⟨y, hys, hyc⟩ := hex σ h
      exact ⟨y, fun _ => ⟨hys, hyc⟩⟩
    · exact ⟨0, fun hh => absurd hh h⟩
  let φ : (Fin (atomsOf X).length → Sign) → (Fin k → ℝ) := fun σ => (hex2 σ).choose
  have hφmem : ∀ σ ∈ (goodCells X).toFinset, φ σ ∈ s := by
    intro σ hσ
    exact ((hex2 σ).choose_spec hσ).1
  have hφinj : Set.InjOn φ ↑((goodCells X).toFinset) := by
    intro σ hσ τ hτ heq
    by_contra hne
    have hσ' : σ ∈ goodCells X := List.mem_toFinset.mp hσ
    have hτ' : τ ∈ goodCells X := List.mem_toFinset.mp hτ
    have h1 : connectedComponentIn (khovSet X ε).set (khovCellPt X σ) =
        connectedComponentIn (khovSet X ε).set (φ σ) := ((hex2 σ).choose_spec hσ).2
    have h2 : connectedComponentIn (khovSet X ε).set (khovCellPt X τ) =
        connectedComponentIn (khovSet X ε).set (φ τ) := ((hex2 τ).choose_spec hτ).2
    exact hsep σ hσ' τ hτ' hne (by rw [h1, heq, ← h2])
  have hcard : (goodCells X).toFinset.card ≤ s.card := by
    have h1 : ((goodCells X).toFinset.image φ).card = (goodCells X).toFinset.card :=
      Finset.card_image_of_injOn hφinj
    have h2 : (goodCells X).toFinset.image φ ⊆ s := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨σ, hσ, rfl⟩ := hy
      exact hφmem σ hσ
    have h3 := Finset.card_le_card h2
    omega
  have hnodup : (goodCells X).Nodup := by
    rw [goodCells, allSigns]
    exact List.Nodup.filter _ (Finset.nodup_toList _)
  calc (goodCells X).length = (goodCells X).toFinset.card :=
        (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ s.card := hcard
    _ ≤ p.eval (khovSet X ε).deg := hscard
    _ ≤ p.eval (4 * X.deg + 1) := khovEval_mono (by have := khovSet_deg_le X ε; omega)
    _ = (p.comp (Polynomial.C 4 * Polynomial.X + Polynomial.C 1)).eval X.deg := by
        rw [Polynomial.eval_comp]
        congr 1
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]

end Work.WilE5.Cells
