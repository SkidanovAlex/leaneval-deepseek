/-
  `Work.WilE7.coreLT_succ.RankBounds`: the two rank inequalities that make the case analysis of
  `CoreLT_succ` exhaustive.

  For an absolute `Good` stratum `T : Stratum 0 (n + (m+1))` — the frame in which `π_{n+1}` is
  `Work.WilE7.CoreStep.projTop n m` and the vertical coordinate is the last fibre coordinate —
  the `π_n`-rank `projRank T z` (the rank of `basePrLin n (m+1)` on the tangent space) satisfies

  * `projRank T z ≤ dim T` (`projRank_le_dim`), with equality iff `π_n` is an immersion at `z`;
  * `dim T - 1 ≤ projRank T z` **whenever the `π_{n+1}`-rank equals `dim T`**
    (`le_projRank_of_projTop_rank`), i.e. the two cases "graph-like" (`projRank = dim T`) and
    "vertical" (`projRank = dim T - 1`) are exhaustive.

  The second is the correct replacement for the **false** claim
  `ker (projTopLin ∘ absPtLin) ⊆ ker (basePrLin)` of `NOTES_S47_pifam_dichotomy.md` §12 (whose
  containment runs the wrong way, cf. `CoreStep/ProjRankOfTop.lean`): the right statement is the
  *inequality* `finrank (V.map (projTopLin ∘ absPtLin)) ≤ finrank (V.map (basePrLin)) + 1`,
  because `projTopLin w = Fin.snoc (projFirst n (m+1) w) (vert w)`.

  (Consequently a `π_{n+1}`-immersion can only drop the `π_n`-rank by one, and a stratum with
  `dim T = K+1` has `projRank T z = K` everywhere — the "vertical" row of the case analysis.)
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.coreLT_succ.SubStratum
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.CoreStep.SigmaFamDefs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-! ## Two coordinate projections, as linear maps -/

/-- `Fin.init` as a linear map. -/
def initLin (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i : Fin n => LinearMap.proj (R := ℝ) (Fin.castSucc i)

theorem initLin_apply (n : ℕ) (w : Fin (n + 1) → ℝ) : initLin n w = Fin.init w := rfl

/-- Projection to the first `n` coordinates of `ℝ^{n+(m+1)}`. -/
def firstLin (n m : ℕ) : (Fin (n + (m + 1)) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i : Fin n => LinearMap.proj (R := ℝ) (Fin.castAdd (m + 1) i)

theorem firstLin_apply (n m : ℕ) (w : Fin (n + (m + 1)) → ℝ) :
    firstLin n m w = projFirst n (m + 1) w := rfl

/-- `basePrLin n (m+1)` is `firstLin` after the reindexing `absPtLin`. -/
theorem basePrLin_eq_firstLin_comp (n m : ℕ) :
    (MainDesign.basePrLin n (m + 1) : (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      = (firstLin n m).comp (Work.WilE7.CoreStep.absPtLin (n + (m + 1))) := by
  ext v i
  rfl

/-- `Fin.init` of `projTop` is `projFirst`. -/
theorem init_projTopLin (n m : ℕ) (w : Fin (n + (m + 1)) → ℝ) :
    initLin n (Work.WilE7.CoreStep.projTopLin n m w) = firstLin n m w := by
  rw [initLin_apply, Work.WilE7.CoreStep.projTopLin_apply, firstLin_apply,
    Work.WilE7.CoreStep.projTop_init]

/-! ## `finrank` of a `Fin.init`-preimage -/

/-- The `Fin.init`-preimage of a submodule `Q ≤ ℝ^n` has dimension `finrank Q + 1`. -/
theorem finrank_init_comap (n : ℕ) (Q : Submodule ℝ (Fin n → ℝ)) :
    Module.finrank ℝ (Q.comap (initLin n)) = Module.finrank ℝ Q + 1 := by
  let e : Q.comap (initLin n) ≃ₗ[ℝ] (Q × ℝ) :=
    { toFun := fun w => (⟨initLin n (w : Fin (n + 1) → ℝ), w.2⟩,
        (w : Fin (n + 1) → ℝ) (Fin.last n))
      invFun := fun q => ⟨Fin.snoc (q.1 : Fin n → ℝ) q.2, by
        rw [Submodule.mem_comap, initLin_apply, Fin.init_snoc]; exact q.1.2⟩
      left_inv := fun w => by
        ext i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j
          simp only [Fin.snoc_castSucc, initLin_apply]
          rfl
      right_inv := fun q => by
        obtain ⟨⟨q₁, hq₁⟩, q₂⟩ := q
        refine Prod.ext ?_ ?_
        · exact Subtype.ext (by simp [initLin_apply])
        · simp
      map_add' := fun a b => by
        refine Prod.ext ?_ ?_
        · exact Subtype.ext (by simp)
        · simp
      map_smul' := fun c a => by
        refine Prod.ext ?_ ?_
        · exact Subtype.ext (by simp)
        · simp }
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_self]

/-! ## The two inequalities -/

theorem projRank_le_dim {n m : ℕ} (S : Stratum 0 (n + m)) (hS : S.Good)
    {z : Fin (0 + (n + m)) → ℝ} (hz : z ∈ S.X.set) :
    MainDesign.projRank S z ≤ n + m - S.j := by
  have h1 : MainDesign.projRank S z ≤
      Module.finrank ℝ (LinearMap.ker (MainDesign.jac S z)) := Submodule.finrank_map_le _ _
  rw [finrank_ker_jac S hS hz] at h1
  exact h1

/-- **The `π_{n+1}`-rank is at most the `π_n`-rank plus one.** -/
theorem finrank_projTop_map_le {n m : ℕ} (T : Stratum 0 (n + (m + 1)))
    (z : Fin (0 + (n + (m + 1))) → ℝ) :
    Module.finrank ℝ ((LinearMap.ker (MainDesign.jac T z)).map
        ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))))
      ≤ MainDesign.projRank T z + 1 := by
  set V : Submodule ℝ (Fin (0 + (n + (m + 1))) → ℝ) := LinearMap.ker (MainDesign.jac T z) with hV
  set V₀ : Submodule ℝ (Fin (n + (m + 1)) → ℝ) :=
    V.map (Work.WilE7.CoreStep.absPtLin (n + (m + 1))) with hV₀
  have hmapA : V.map ((Work.WilE7.CoreStep.projTopLin n m).comp
      (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))
      = V₀.map (Work.WilE7.CoreStep.projTopLin n m) := by
    rw [Submodule.map_comp, hV₀]
  have hproj : MainDesign.projRank T z = Module.finrank ℝ (V₀.map (firstLin n m)) := by
    show Module.finrank ℝ
        ((LinearMap.ker (MainDesign.jac T z)).map (MainDesign.basePrLin n (m + 1)))
      = Module.finrank ℝ (V₀.map (firstLin n m))
    rw [basePrLin_eq_firstLin_comp n m, Submodule.map_comp, ← hV]
  rw [hmapA, hproj]
  have hle : V₀.map (Work.WilE7.CoreStep.projTopLin n m) ≤
      (V₀.map (firstLin n m)).comap (initLin n) := by
    intro w hw
    rw [Submodule.mem_comap]
    obtain ⟨v, hv, rfl⟩ := hw
    rw [init_projTopLin]
    exact Submodule.mem_map_of_mem hv
  calc Module.finrank ℝ (V₀.map (Work.WilE7.CoreStep.projTopLin n m))
      ≤ Module.finrank ℝ ((V₀.map (firstLin n m)).comap (initLin n)) :=
        Submodule.finrank_mono hle
    _ = Module.finrank ℝ (V₀.map (firstLin n m)) + 1 := finrank_init_comap n _

/-- **A `Good` sub-stratum has at least as many equations.**  For absolute `Good` strata
`S ⊆ T`, `T.j ≤ S.j` (equivalently `dim S ≤ dim T`): the tangent space of `S` is contained in
that of `T`, and both equations families have full rank. -/
theorem j_le_of_sub {N : ℕ} (S T : Stratum 0 N) (hS : S.Good) (hT : T.Good)
    (hsub : S.X.set ⊆ T.X.set) {z : Fin (0 + N) → ℝ} (hz : z ∈ S.X.set) : T.j ≤ S.j := by
  have hker := ker_jac_le_ker_jac S T hS hT hsub hz
  have h1 : Module.finrank ℝ (LinearMap.ker (jac S z)) ≤
      Module.finrank ℝ (LinearMap.ker (jac T z)) := Submodule.finrank_mono hker
  rw [finrank_ker_jac S hS hz, finrank_ker_jac T hT (hsub hz)] at h1
  have hSle : S.j ≤ N := Work.CoreStep.Stratum.j_le_card_of_good S hS ⟨z, hz⟩
  have hTle : T.j ≤ N := Work.CoreStep.Stratum.j_le_card_of_good T hT ⟨z, hsub hz⟩
  omega

/-- **The `π_{n+1}`-rank equals `dim T` forces the `π_n`-rank to be at least `dim T - 1`.** -/
theorem le_projRank_of_projTop_rank {n m : ℕ} (T : Stratum 0 (n + (m + 1)))
    {z : Fin (0 + (n + (m + 1))) → ℝ}
    (h : Module.finrank ℝ ((LinearMap.ker (MainDesign.jac T z)).map
        ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))))
      = n + (m + 1) - T.j) :
    n + (m + 1) - T.j - 1 ≤ MainDesign.projRank T z := by
  have := finrank_projTop_map_le T z
  omega

end Work.WilE7.coreLT_succ
