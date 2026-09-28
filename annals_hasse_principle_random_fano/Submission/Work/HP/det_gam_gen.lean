import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_satLat
import Submission.Work.HP.numaux.detL_le_of_le
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.gcdMinors2_linear
import Submission.Work.HP.detgam_gcdMinors2_basis_prim
import Submission.Work.HP.detgam_span_coords_detL
import Submission.Work.HP.detgam_span_pair_wedgeNorm
import Submission.Work.HP.MDEstimates.orthLat_detL

/-!
# `Work.HP.det_gam_gen`

Generalisation of `Work.HP.det_gam` from `Fin (n+1) → ℤ` to an arbitrary finite index type
`ι` (in an arbitrary universe).  For two `ℤ`-linearly independent integer vectors `c, d : ι → ℤ`,

* `detL (latOrth c ⊓ latOrth d) = wedgeNorm c d / gcdMinors2 c d`, and
* `dmin 2 {c, d} = detL (latOrth c ⊓ latOrth d)`.

Everything is reduced to the saturated rank-two lattice `K := satLat (span_ℤ {c,d})`:

* `Λ_c ∩ Λ_d = K^⊥` (`latOrth_inf_eq_orthLat_sat`) and `detL K^⊥ = detL K`
  (`MDEstimates.orthLat_detL`, the reciprocal-covolume identity for a saturated lattice);
* `detL K = wedgeNorm c d / gcdMinors2 c d` from the covolume-scaling formula
  (`detgam_span_coords_detL`, `detgam_span_pair_wedgeNorm`, `detgam_gcdMinors2_basis_prim`,
  `Lat.gcdMinors2_linear`);
* `dmin 2 {c,d} = detL K`, since every rank-`2` sublattice `L ⊇ {c,d}` satisfies `L ≤ K` with
  equal rank (`exists_smul_le`) and `detL` is antitone under equal-rank inclusion (`detL_le_of_le`).

The copies in the namespace `Work.HP.DGG` below are verbatim transcriptions of the lemmas of
`Submission/Work/HP/det_gam.lean`, `Submission/Work/HP/detgam_exists_smul_le.lean` and
`Submission/Work/HP/numaux/detL_le_of_le.lean`, made universe-polymorphic: those files state their
results for `{ι : Type}` (universe `0`) whereas the target here quantifies over `{ι : Type*}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP

namespace DGG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The rank of the saturation -/

/-- The saturation of an integral lattice has the same rank. -/
lemma rk_satLat (Λ : Submodule ℤ (ι → ℤ)) : rk (satLat Λ) = rk Λ := by
  show Module.finrank ℤ (satLat Λ) = Module.finrank ℤ Λ
  rw [numaux.finrank_eq_finrank_spread (satLat Λ), numaux.finrank_eq_finrank_spread Λ,
    numaux.spread_satLat_eq]

/-! ## Elementary facts about `latOrth`, `gcdMinors2` and `satLat` -/

/-- Membership in `latOrth c`, in terms of the explicit pairing. -/
lemma mem_latOrth_iff (c y : ι → ℤ) : y ∈ latOrth c ↔ ∑ i, y i * c i = 0 := by
  rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply]
  simp

/-- The gcd of the `2 × 2` minors is nonnegative. -/
lemma gcdMinors2_nonneg (c d : ι → ℤ) : 0 ≤ gcdMinors2 c d := by
  have h : |gcdMinors2 c d| = gcdMinors2 c d := by
    rw [Int.abs_eq_normalize, gcdMinors2, Finset.normalize_gcd]
  exact h ▸ abs_nonneg _

/-- Two `ℤ`-linearly independent vectors do not have all their `2 × 2` minors vanishing. -/
lemma gcdMinors2_ne_zero (c d : ι → ℤ) (h : LinearIndependent ℤ ![c, d]) :
    gcdMinors2 c d ≠ 0 := by
  intro h0
  have hall : ∀ i j : ι, c i * d j - c j * d i = 0 := by
    intro i j
    have := Finset.gcd_eq_zero_iff.mp (by rw [← gcdMinors2]; exact h0) (i, j) (Finset.mem_univ _)
    simpa using this
  have hc0 : c ≠ 0 := h.ne_zero 0
  obtain ⟨i0, hi0⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc0 (funext hcon)
  have hrel : ∑ i : Fin 2, (![-(d i0), c i0] : Fin 2 → ℤ) i • ![c, d] i = 0 := by
    rw [Fin.sum_univ_two]
    have e1 : (![-(d i0), c i0] : Fin 2 → ℤ) 0 • ![c, d] 0 = (-(d i0)) • c := by
      simp [Matrix.cons_val_zero]
    have e2 : (![-(d i0), c i0] : Fin 2 → ℤ) 1 • ![c, d] 1 = (c i0) • d := by
      simp [Matrix.cons_val_one]
    rw [e1, e2]
    ext j
    simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (hall i0 j)
  have h1 := Fintype.linearIndependent_iff.mp h ![-(d i0), c i0] hrel 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
  exact hi0 h1

/-- The gcd of the `2 × 2` minors is positive for independent `c, d`. -/
lemma gcdMinors2_pos (c d : ι → ℤ) (h : LinearIndependent ℤ ![c, d]) :
    0 < gcdMinors2 c d :=
  lt_of_le_of_ne (gcdMinors2_nonneg c d) (Ne.symm (gcdMinors2_ne_zero c d h))

/-! ## `latOrth c ⊓ latOrth d` is the orthogonal lattice of the saturation -/

/-- The intersection of the two orthogonal lattices depends only on the saturation of the pair:
`Λ_c ∩ Λ_d = K^⊥` for `K = satLat (span_ℤ {c,d})`. -/
lemma latOrth_inf_eq_orthLat_sat (c d : ι → ℤ) :
    latOrth c ⊓ latOrth d = orthLat (satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ)))) := by
  ext y
  rw [Submodule.mem_inf, mem_latOrth_iff, mem_latOrth_iff, mem_orthLat]
  constructor
  · rintro ⟨h1, h2⟩ z hz
    rw [mem_satLat] at hz
    obtain ⟨m, hm, hmz⟩ := hz
    rw [Submodule.mem_span_pair] at hmz
    obtain ⟨a, b, hab⟩ := hmz
    have key : m * dotI y z = 0 := by
      rw [← dotI_smul_right m y z, ← hab, dotI_add_right, dotI_smul_right, dotI_smul_right,
        show dotI y c = 0 from h1, show dotI y d = 0 from h2]
      ring
    exact (mul_eq_zero.mp key).resolve_left hm
  · intro h
    have hc : c ∈ satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) := by
      refine le_satLat _ (Submodule.subset_span ?_)
      simp
    have hd : d ∈ satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) := by
      refine le_satLat _ (Submodule.subset_span ?_)
      simp
    exact ⟨h c hc, h d hd⟩

/-- The rank of the span of an independent pair. -/
lemma rk_span_pair (c d : ι → ℤ) (h : LinearIndependent ℤ ![c, d]) :
    rk (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) = 2 := by
  have hrange : (Set.range ![c, d]) = ({c, d} : Set (ι → ℤ)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases hx with hx | hx
      · exact ⟨0, by simpa using hx.symm⟩
      · exact ⟨1, by simpa using hx.symm⟩
  show Module.finrank ℤ (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) = 2
  rw [← hrange, finrank_span_eq_card h, Fintype.card_fin]

/-- The rank of the saturation of the span of an independent pair is `2`. -/
lemma rk_sat_span_pair (c d : ι → ℤ) (h : LinearIndependent ℤ ![c, d]) :
    rk (satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ)))) = 2 := by
  have h0 := rk_satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ)))
  rw [h0]
  exact rk_span_pair c d h

/-- A `ℤ`-basis indexed by `Fin 2` of a rank-`2` lattice. -/
noncomputable def basisOfRkTwo (L : Submodule ℤ (ι → ℤ)) (h : rk L = 2) :
    Module.Basis (Fin 2) ℤ L :=
  let s := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  have hn : s.1 = 2 := by
    have h1 : Module.finrank ℤ L = Fintype.card (Fin s.1) := Module.finrank_eq_card_basis s.2
    rw [Fintype.card_fin] at h1
    rw [← h1]
    exact h
  s.2.reindex (Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_fin]; exact hn))

/-! ## Equal-rank inclusion is a finite-index inclusion -/

/-- Two submodules of `ℤ^ι` of the same finite `ℤ`-rank, one contained in the other, differ by a
finite index: a single nonzero integer kills the quotient.  (Generalisation of
`Work.HP.detgam_exists_smul_le`.) -/
lemma exists_smul_le {P L : Submodule ℤ (ι → ℤ)} (hPL : P ≤ L) (hrk : rk P = rk L) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ L, m • x ∈ P := by
  have hrk' : Module.finrank ℤ P = Module.finrank ℤ L := hrk
  let P' : Submodule ℤ L := P.comap L.subtype
  have hP' : Module.finrank ℤ P' = Module.finrank ℤ P :=
    (Submodule.comapSubtypeEquivOfLe hPL).finrank_eq
  have hquot : Module.finrank ℤ (L ⧸ P') = 0 := by
    have h := Submodule.finrank_quotient_add_finrank P'
    omega
  have htors : Module.IsTorsion ℤ (L ⧸ P') :=
    (Module.finrank_eq_zero_iff_isTorsion).mp hquot
  obtain ⟨m, hm⟩ := Submodule.annihilator_top_inter_nonZeroDivisors (M := L ⧸ P') htors
  have hm0 : m ≠ 0 := fun h => zero_notMem_nonZeroDivisors (h ▸ hm.2)
  refine ⟨m, hm0, ?_⟩
  intro x hx
  have hann : m • (Submodule.Quotient.mk (p := P') (⟨x, hx⟩ : L)) = 0 :=
    Submodule.mem_annihilator.mp hm.1 (Submodule.Quotient.mk (p := P') (⟨x, hx⟩ : L))
      Submodule.mem_top
  have hmem : (m • (⟨x, hx⟩ : L)) ∈ P' := by
    rw [← Submodule.Quotient.mk_eq_zero P']
    rw [← Submodule.mkQ_apply]
    rw [map_smul, Submodule.mkQ_apply]
    exact hann
  have h2 := Submodule.mem_comap.mp hmem
  simpa using h2

/-! ## `detL` is antitone under equal-rank inclusion -/

/-- (Generalisation of `Work.HP.numaux.detL_le_of_le`.) -/
theorem detL_le_of_le {M L : Submodule ℤ (ι → ℤ)}
    (h : M ≤ L) (hr : rk M = rk L) : detL L ≤ detL M := by
  classical
  obtain ⟨nL, bL⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  obtain ⟨nM, bM0⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) M
  have hnL : rk L = nL := by
    have := Module.finrank_eq_card_basis bL
    simpa [rk] using this
  have hnM : rk M = nM := by
    have := Module.finrank_eq_card_basis bM0
    simpa [rk] using this
  have hn : nL = nM := by rw [← hnL, ← hr, hnM]
  let bM : Module.Basis (Fin nL) ℤ M := bM0.reindex (finCongr hn).symm
  have hle : (Work.HP.gramMat nL L bL).det ≤ (Work.HP.gramMat nL M bM).det :=
    numaux.gramMat_det_le h bL bM
  have hL : detL L = Real.sqrt (Work.HP.gramMat nL L bL).det :=
    Work.HP.Lat.detL_basis_gram L bL
  have hM : detL M = Real.sqrt (Work.HP.gramMat nL M bM).det :=
    Work.HP.Lat.detL_basis_gram M bM
  rw [hL, hM]
  exact Real.sqrt_le_sqrt hle

/-! ## The determinant of the saturation of a pair -/

/-- `detL (satLat (span_ℤ {c,d})) = wedgeNorm c d / gcdMinors2 c d` for `ℤ`-independent `c, d`.
(Generalisation of `Work.HP.detL_sat_span_pair`.) -/
lemma detL_sat_span_pair (c d : ι → ℤ) (h : LinearIndependent ℤ ![c, d]) :
    detL (satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ))))
      = wedgeNorm c d / (gcdMinors2 c d : ℝ) := by
  set K := satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) with hKdef
  have hK : IsPrimLat K := isPrimLat_satLat _
  have hc : c ∈ K := le_satLat _ (Submodule.subset_span (by simp))
  have hd : d ∈ K := le_satLat _ (Submodule.subset_span (by simp))
  have hrk : rk K = 2 := rk_sat_span_pair c d h
  let b : Module.Basis (Fin 2) ℤ K := basisOfRkTwo K hrk
  have hmem : ∀ i : Fin 2, ![c, d] i ∈ K := by
    intro i
    fin_cases i
    · simpa using hc
    · simpa using hd
  set A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => (b.repr ⟨![c, d] i, hmem i⟩) j with hA
  have hA0 : ∀ j, A 0 j = (b.repr ⟨c, hc⟩) j := by
    intro j
    have hsub : (⟨![c, d] 0, hmem 0⟩ : K) = ⟨c, hc⟩ := Subtype.ext (by simp)
    rw [hA]
    simp only [Matrix.of_apply, hsub]
  have hA1 : ∀ j, A 1 j = (b.repr ⟨d, hd⟩) j := by
    intro j
    have hsub : (⟨![c, d] 1, hmem 1⟩ : K) = ⟨d, hd⟩ := Subtype.ext (by simp)
    rw [hA]
    simp only [Matrix.of_apply, hsub]
  have hexp : ∀ i : Fin 2, A i 0 • (b 0 : ι → ℤ) + A i 1 • (b 1 : ι → ℤ) = ![c, d] i := by
    intro i
    have h1 := Module.Basis.sum_repr b (⟨![c, d] i, hmem i⟩ : K)
    rw [Fin.sum_univ_two] at h1
    have h2 : (Submodule.subtype K) ((b.repr ⟨![c, d] i, hmem i⟩) 0 • b 0
        + (b.repr ⟨![c, d] i, hmem i⟩) 1 • b 1) = ![c, d] i := by
      rw [h1]
      rfl
    have h3 : (b.repr ⟨![c, d] i, hmem i⟩) 0 • ((b 0 : K) : ι → ℤ)
        + (b.repr ⟨![c, d] i, hmem i⟩) 1 • ((b 1 : K) : ι → ℤ) = ![c, d] i := by
      simpa using h2
    simpa only [hA, Matrix.of_apply] using h3
  have h0 : A 0 0 • (b 0 : ι → ℤ) + A 0 1 • (b 1 : ι → ℤ) = c := by
    simpa using hexp 0
  have h1 : A 1 0 • (b 0 : ι → ℤ) + A 1 1 • (b 1 : ι → ℤ) = d := by
    simpa using hexp 1
  have hgcd : gcdMinors2 c d = |A.det| := by
    rw [← h0, ← h1, Work.HP.Lat.gcdMinors2_linear, detgam_gcdMinors2_basis_prim K hK b, mul_one,
      Matrix.det_fin_two, Int.natCast_natAbs]
  have hsc := detgam_span_coords_detL K b c d hc hd h
  have hw := detgam_span_pair_wedgeNorm c d h
  have hTdet : (b.repr ⟨c, hc⟩) 0 * (b.repr ⟨d, hd⟩) 1
      - (b.repr ⟨c, hc⟩) 1 * (b.repr ⟨d, hd⟩) 0 = A.det := by
    rw [Matrix.det_fin_two, ← hA0 0, ← hA1 1, ← hA0 1, ← hA1 0]
  rw [hTdet] at hsc
  have hcast : (((|A.det| : ℤ)) : ℝ) = (gcdMinors2 c d : ℝ) := by rw [← hgcd]
  rw [hcast] at hsc
  have hg : (gcdMinors2 c d : ℝ) ≠ 0 := by
    have h0' := gcdMinors2_ne_zero c d h
    exact_mod_cast h0'
  have hmain : wedgeNorm c d = (gcdMinors2 c d : ℝ) * detL K := by
    rw [← hw]
    exact hsc
  rw [eq_div_iff hg, hmain, mul_comm]

/-! ## `dmin` of a pair equals the determinant of the saturation -/

/-- Every rank-`2` sublattice of `ℤ^ι` containing `c` and `d` lies in the saturation of their
span. -/
lemma le_sat_of_le_of_rk_eq (c d : ι → ℤ) (h : LinearIndependent ℤ ![c, d])
    {L : Submodule ℤ (ι → ℤ)} (hrk : rk L = 2) (hsub : ({c, d} : Set (ι → ℤ)) ⊆ L) :
    L ≤ satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) := by
  have hrkP : rk (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) = 2 := rk_span_pair c d h
  have hPL : Submodule.span ℤ ({c, d} : Set (ι → ℤ)) ≤ L := by
    rw [Submodule.span_le]
    intro x hx
    exact hsub hx
  intro x hx
  obtain ⟨m, hm, hmx⟩ := exists_smul_le hPL (by rw [hrkP, hrk])
  exact mem_satLat.mpr ⟨m, hm, hmx x hx⟩

/-- `dmin 2 {c,d}` is the determinant of the saturation of the span of `c, d`.
(Generalisation of `Work.HP.dmin_pair_eq_detL_sat`.) -/
lemma dmin_pair_eq_detL_sat (c d : ι → ℤ) (h : LinearIndependent ℤ ![c, d]) :
    dmin 2 ({c, d} : Set (ι → ℤ))
      = detL (satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ)))) := by
  set K := satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ))) with hKdef
  have hrkK : rk K = 2 := rk_sat_span_pair c d h
  have hmemK : detL K ∈ {D : ℝ | ∃ L : Submodule ℤ (ι → ℤ),
      rk L = 2 ∧ ({c, d} : Set (ι → ℤ)) ⊆ L ∧ detL L = D} :=
    ⟨K, hrkK, fun x hx => le_satLat _ (Submodule.subset_span hx), rfl⟩
  have hbound : ∀ D ∈ {D : ℝ | ∃ L : Submodule ℤ (ι → ℤ),
      rk L = 2 ∧ ({c, d} : Set (ι → ℤ)) ⊆ L ∧ detL L = D}, detL K ≤ D := by
    rintro D ⟨L, hrkL, hsub, rfl⟩
    exact detL_le_of_le (le_sat_of_le_of_rk_eq c d h hrkL hsub) (by rw [hrkK, hrkL])
  show sInf {D : ℝ | ∃ L : Submodule ℤ (ι → ℤ), rk L = 2 ∧ ({c, d} : Set (ι → ℤ)) ⊆ L
      ∧ detL L = D} = detL K
  exact le_antisymm (csInf_le ⟨detL K, hbound⟩ hmemK) (le_csInf ⟨_, hmemK⟩ hbound)

end DGG

/-! ## The main statement -/

theorem det_gam_gen {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ι → ℤ)
    (h : LinearIndependent ℤ ![c, d]) :
    detL (latOrth c ⊓ latOrth d) = wedgeNorm c d / (gcdMinors2 c d : ℝ) ∧
    dmin 2 ({c, d} : Set (ι → ℤ)) = detL (latOrth c ⊓ latOrth d) := by
  have horth := DGG.latOrth_inf_eq_orthLat_sat c d
  have hdet := DGG.detL_sat_span_pair c d h
  have hdu := MDEstimates.orthLat_detL (satLat (Submodule.span ℤ ({c, d} : Set (ι → ℤ))))
    (isPrimLat_satLat _)
  have hdmin := DGG.dmin_pair_eq_detL_sat c d h
  exact ⟨by rw [horth, hdu, hdet], by rw [hdmin, horth, hdu]⟩

end Work.HP
