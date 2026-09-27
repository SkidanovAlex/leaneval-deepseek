import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Drive.trailStDef
import Submission.Work.Drive.trailBase
import Submission.Work.Drive.trailStep.stepStCore
import Submission.Work.Drive.trailTools

/-!
# The piece family of the trail recursion

From the states produced by `Work.Drive.baseSt` and `Work.Drive.trailStep.stepStCore` we extract the
`ℕ`-indexed family of pieces feeding `Work.Noncompact.CompressionTube.ray_of_pieces_with_germs`.
-/

namespace Work.Drive

open Set Filter
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (Work.Noncompact.CompressionTube.MC n)
    Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]

/-- **The piece family.**  An escaping path in an open set `W` of an `n`-manifold (`n ≥ 2`) yields
a family of smooth immersed pieces with matching straight germs at the junctions, pairwise meeting
only at the junctions, inside `W` and escaping every compact set. -/
theorem rayPieceFamilyTrail (hn : 2 ≤ n) {W : Set M} (hW : IsOpen W) {ρ : ℝ → M}
    (hρ : Continuous ρ) (hρ0 : ρ 0 ∈ W) (hρW : ∀ t : ℝ, 0 ≤ t → ρ t ∈ W)
    (hρesc : ∀ K : Set M, IsCompact K → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ρ t ∉ K) :
    ∃ (P : ℕ → ℝ → M) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (u : EuclideanSpace ℝ (Fin n)) (e : ℝ),
      P 0 0 = ρ 0 ∧ 0 < e ∧ e ≤ 1 ∧ u ≠ 0 ∧
      c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧ ρ 0 ∈ c.source ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → P 0 t = c.symm (c (ρ 0) + t • u)) ∧
      (∀ i : ℕ, ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder (P i)) ∧
      (∀ (i : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 → Function.Injective
        (mfderiv Work.Noncompact.CompressionTube.MCreal
          (Work.Noncompact.CompressionTube.MC n) (P i) t)) ∧
      (∀ i : ℕ, Set.InjOn (P i) (Set.Icc (0:ℝ) 1)) ∧
      (∀ i : ℕ, P i 1 = P (i + 1) 0) ∧
      (∀ i : ℕ, P i '' Set.Icc (0:ℝ) 1 ⊆ W) ∧
      (∀ i : ℕ, ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
          (u' : EuclideanSpace ℝ (Fin n)) (e' : ℝ),
        0 < e' ∧ c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
          Work.Noncompact.CompressionTube.smoothOrder M ∧ P i 1 ∈ c'.source ∧
        (∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → P i t = c'.symm (c' (P i 1) + (t - 1) • u')) ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ e' → P (i + 1) t = c'.symm (c' (P (i + 1) 0) + t • u'))) ∧
      (∀ i j : ℕ, i < j →
        P i '' Set.Icc (0:ℝ) 1 ∩ P j '' Set.Icc (0:ℝ) 1 ⊆ {P i 1}) ∧
      (∀ K : Set M, IsCompact K → ∃ I : ℕ, ∀ i : ℕ, I ≤ i →
        P i '' Set.Icc (0:ℝ) 1 ∩ K = ∅) := by
  classical
  haveI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  set Kex : CompactExhaustion M := CompactExhaustion.choice M with hKexdef
  -- the states
  have hstep : ∀ S : St (n := n) (M := M) W ρ Kex,
      ∃ (S' : St (n := n) (M := M) W ρ Kex) (ein : ℝ),
        S'.k = S.k + 1 ∧ (∀ j ≤ S.k, S'.P j = S.P j) ∧ 0 < ein ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ ein →
          S'.P (S.k + 1) t = S.c.symm (S.c S.x + t • S.w)) ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ ein → S.c S.x + t • S.w ∈ S.c.target) :=
    fun S => Work.Drive.trailStep.stepStCore (n := n) (M := M) hn hW hρ hρW hρesc Kex S
  obtain ⟨B, hBk⟩ := baseSt (n := n) (M := M) hn hW hρ hρW hρesc Kex
  let Sseq : ℕ → St (n := n) (M := M) W ρ Kex :=
    fun i => Nat.rec B (fun _ S => Classical.choose (hstep S)) i
  have hSseq_succ : ∀ i : ℕ, Sseq (i + 1) = Classical.choose (hstep (Sseq i)) := fun i => rfl
  have hspec : ∀ i : ℕ, (Sseq (i + 1)).k = (Sseq i).k + 1 ∧
      (∀ j ≤ (Sseq i).k, (Sseq (i + 1)).P j = (Sseq i).P j) ∧
      0 < Classical.choose (Classical.choose_spec (hstep (Sseq i))) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ Classical.choose (Classical.choose_spec (hstep (Sseq i))) →
        (Sseq (i + 1)).P ((Sseq i).k + 1) t =
          (Sseq i).c.symm ((Sseq i).c (Sseq i).x + t • (Sseq i).w)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ Classical.choose (Classical.choose_spec (hstep (Sseq i))) →
        (Sseq i).c (Sseq i).x + t • (Sseq i).w ∈ (Sseq i).c.target) := by
    intro i
    rw [hSseq_succ i]
    exact Classical.choose_spec (Classical.choose_spec (hstep (Sseq i)))
  have hkstate : ∀ i : ℕ, (Sseq i).k = i := by
    intro i
    induction i with
    | zero => exact hBk
    | succ i ih => rw [(hspec i).1, ih]
  have hpiece' : ∀ i : ℕ, (Sseq (i + 1)).P (i + 1) = (Sseq (i + 1)).P ((Sseq i).k + 1) := by
    intro i
    rw [show (Sseq i).k + 1 = i + 1 from by rw [hkstate i]]
  have hcons : ∀ i j : ℕ, j ≤ i → (Sseq i).P j = (Sseq j).P j := by
    intro i
    induction i with
    | zero =>
        intro j hj
        rw [Nat.le_zero.mp hj]
    | succ i ih =>
        intro j hj
        rcases lt_or_ge j (i + 1) with hlt | hge
        · have hj' : j ≤ i := by omega
          exact ((hspec i).2.1 j (by rw [hkstate i]; exact hj')).trans (ih j hj')
        · have hje : j = i + 1 := le_antisymm hj hge
          rw [hje]
  have hxjun : ∀ i : ℕ, (Sseq i).P i 1 = (Sseq i).x := by
    intro i
    have h := (Sseq i).hger 1 (by linarith [(Sseq i).he]) le_rfl
    have h2 : (Sseq i).P (Sseq i).k 1 = (Sseq i).x := by
      rw [h]
      simp only [sub_self, zero_smul, add_zero]
      exact (Sseq i).c.left_inv (Sseq i).hxc
    rwa [hkstate i] at h2
  -- the junction point of the next piece
  have hJ : ∀ i : ℕ, (Sseq (i + 1)).P (i + 1) 0 = (Sseq i).x := by
    intro i
    rw [hpiece' i]
    have h0 := (hspec i).2.2.2.1 0 le_rfl (le_of_lt (hspec i).2.2.1)
    rw [h0]
    simp only [zero_smul, add_zero]
    exact (Sseq i).c.left_inv (Sseq i).hxc
  refine ⟨fun i => (Sseq i).P i, B.c₀, B.u₀, min B.e₀ 1, ?_, lt_min B.he₀ one_pos, min_le_right _ _,
    B.hu₀, B.hc₀, B.hρ0₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show B.P 0 0 = ρ 0
    exact B.hP0
  · intro t ht0 hte
    exact B.hgerm₀ t ht0 (hte.trans (min_le_left _ _))
  · intro i
    beta_reduce
    exact (Sseq i).hPsm i (le_of_eq (hkstate i).symm)
  · intro i t ht
    beta_reduce
    exact (Sseq i).hPimm i (le_of_eq (hkstate i).symm) t ht
  · intro i
    beta_reduce
    exact (Sseq i).hPinj i (le_of_eq (hkstate i).symm)
  · intro i
    dsimp only []
    rw [hxjun i]
    exact (hJ i).symm
  · intro i
    beta_reduce
    exact (Sseq i).hPW i (le_of_eq (hkstate i).symm)
  · intro i
    have hei : 0 < Classical.choose (Classical.choose_spec (hstep (Sseq i))) := (hspec i).2.2.1
    refine ⟨(Sseq i).c, (Sseq i).w,
      min ((Sseq i).e) (Classical.choose (Classical.choose_spec (hstep (Sseq i)))),
      lt_min (Sseq i).he hei, (Sseq i).hc, ?_, ?_, ?_⟩
    · beta_reduce
      rw [hxjun i]
      exact (Sseq i).hxc
    · intro t ht1 ht2
      have hlt : 1 - (Sseq i).e ≤ t := by
        linarith [min_le_left ((Sseq i).e)
          (Classical.choose (Classical.choose_spec (hstep (Sseq i))))]
      have hger' := (Sseq i).hger t hlt ht2
      dsimp only
      rw [hxjun i]
      rw [show (Sseq i).P i = (Sseq i).P (Sseq i).k from by rw [hkstate i]]
      exact hger'
    · intro t ht0 ht1
      beta_reduce
      rw [hJ i, hpiece' i]
      exact (hspec i).2.2.2.1 t ht0 (ht1.trans (min_le_right _ _))
  · intro i j hij
    have hci : (Sseq j).P i = (Sseq i).P i := hcons j i (le_of_lt hij)
    dsimp only
    rw [← hci]
    refine (Sseq j).hPsep i j hij ?_
    have := hkstate j
    omega
  · intro K hK
    obtain ⟨N, hN⟩ := Kex.exists_superset_of_isCompact hK
    refine ⟨max N 1, fun i hi => ?_⟩
    have h1 : 1 ≤ i := le_trans (le_max_right N 1) hi
    have h2 : i ≤ (Sseq i).k := le_of_eq (hkstate i).symm
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact (Set.disjoint_left.mp ((Sseq i).hPlev i h1 h2) hy1)
        (Kex.subset (by omega) (hN hy2))
    · intro h
      exact absurd h (Set.notMem_empty y)

end Work.Drive
