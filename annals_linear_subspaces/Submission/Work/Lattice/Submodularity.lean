import Mathlib
import Submission.Work.Lattice.GraysonLattice
import Submission.Work.Lattice.PresentationLattice
import Submission.Work.Polygon.GraysonEndpoints

/-!
# P2-general (i): log-covol submodularity for FULL-RANK subgroups — the index route

The naive aligned-`ℤ`-basis engine for the covolume submodularity
(`GraysonData.graysonData_log_submodularity`, which needs bases of `W₁`, `W₂` extending
a common basis of `W₁ ⊓ W₂`) does **not** apply to arbitrary subgroups of a lattice:
over `ℤ` a basis of `W₁ ⊓ W₂` need not extend to bases of `W₁`, `W₂` (e.g. `6ℤ` inside
`ℤ`; `2ℤ` is not a direct summand of `ℤ`).  For **full-rank** subgroups of a full-rank
lattice the correct identity is purely index-theoretic:

    `[Λ : V] · [Λ : W] = [Λ : V ⊓ W] · [Λ : V ⊔ W]`

(index multiplicativity of additive subgroups), which through
`ZLattice.covolume_div_covolume_eq_relIndex'` gives the **exact covolume identity**

    `covol(V) · covol(W) = covol(V ⊓ W) · covol(V ⊔ W)`

for full-rank `V, W ≤ Λ` (ambient covolumes; for full-rank subgroups these agree with
the intrinsic `latticeCovol` of the Grayson-data vocabulary, since their real span is the
whole space).

This module records:
1. the additive-group index multiplicativity (pure group theory),
2. the instance plumbing (`DiscreteTopology`/`IsZLattice` for subgroups of a full-rank
   lattice `Λ` given their real rank `subDim = d`), including the finite-index argument
   that `V ⊓ W` is again full-rank (`relIndex_inf_ne_zero` + the annihilator
   `AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero` + the `ℤ`-basis of `Λ`),
3. the ambient covolume product identity `covolume_mul_eq_inf_sup`.

The full **mixed-rank** submodularity of paper Lemma 3 (with the quadratic
`A·k(d−k)` term over all discrete subgroups) is NOT obtained here: it needs an
elementary-divisor / relative-basis development over `ℤ` (Smith normal form), recorded
in the ROADMAP as an open dependency of the general Harder–Narasimhan layer.

All declarations are Mathlib + Submission (GraysonLattice/PresentationLattice) only.
-/

noncomputable section

open Set Module Real MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.Submodularity

open Submission.GraysonLattice
open Submission.GraysonData

/-! ## 1. Additive-group index multiplicativity -/

/-- **Index multiplicativity**: for subgroups `H, K ≤ G` of an additive group,
`[G : H]·[G : K] = [G : H ⊓ K]·[G : H ⊔ K]` (in `relIndex` notation: the relative index
of `H` in `G` is the index of `H ∩ G = H` in `G`). -/
theorem relIndex_mul_eq_inf_sup {A : Type*} [AddCommGroup A] (H K G : AddSubgroup A)
    (hHG : H ≤ G) (hKG : K ≤ G) :
    H.relIndex G * K.relIndex G = (H ⊓ K).relIndex G * (H ⊔ K).relIndex G := by
  have hsup : H ⊔ K ≤ G := sup_le hHG hKG
  have hT3 : (H ⊓ K).relIndex G = K.relIndex H * H.relIndex G := by
    have hc := AddSubgroup.relIndex_mul_relIndex (H := H ⊓ K) (K := H) (L := G) inf_le_left hHG
    rw [AddSubgroup.inf_relIndex_left] at hc
    exact hc.symm
  have hT2 : K.relIndex G = K.relIndex H * (H ⊔ K).relIndex G := by
    have hc := AddSubgroup.relIndex_mul_relIndex (H := K) (K := H ⊔ K) (L := G) le_sup_right hsup
    rw [AddSubgroup.relIndex_sup_right (H := H) (K := K)] at hc
    exact hc.symm
  calc
    H.relIndex G * K.relIndex G = H.relIndex G * (K.relIndex H * (H ⊔ K).relIndex G) := by
      rw [hT2]
    _ = (K.relIndex H * H.relIndex G) * (H ⊔ K).relIndex G := by ring
    _ = (H ⊓ K).relIndex G * (H ⊔ K).relIndex G := by rw [hT3]

/-! ## 2. Subgroup topology/rank plumbing for a full-rank ambient lattice -/

/-- Discreteness inherits to subgroups: `V ≤ Λ` with `Λ` discrete makes `V` discrete. -/
lemma discreteTopology_of_le {d : ℕ} (Λ V : Submodule ℤ (E d)) [DiscreteTopology Λ]
    (hVΛ : V ≤ Λ) : DiscreteTopology V := by
  exact DiscreteTopology.of_subset (s := (Λ : Set (E d))) (t := (V : Set (E d)))
    inferInstance (by intro x hx; exact hVΛ hx)

/-- A subgroup whose real span has full dimension `d` spans the whole space. -/
lemma realSpan_eq_top_of_subDim {d : ℕ} (W : Submodule ℤ (E d)) (h : subDim W = d) :
    realSpan W = ⊤ := by
  dsimp [subDim] at h
  exact Submodule.eq_top_of_finrank_eq (by
    have hE : Module.finrank ℝ (E d) = d := by
      have hb := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      simpa using (hb.finrank_eq (Fin d))
    simpa [hE] using h)

/-- The `IsZLattice` instance for a discrete full-rank subgroup of the ambient space. -/
lemma isZLattice_of_subDim {d : ℕ} (W : Submodule ℤ (E d))
    [DiscreteTopology W] (hWdim : subDim W = d) : IsZLattice ℝ W := by
  exact ⟨realSpan_eq_top_of_subDim W hWdim⟩

/-- The ambient covolume of a full-rank subgroup `X ≤ Λ` is `covol(Λ)` times its index:
`covol X = covol Λ · [Λ : X]`. -/
lemma covol_eq_covol_lattice_mul_relIndex {d : ℕ} (Λ X : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] [DiscreteTopology X] [IsZLattice ℝ X]
    (hXΛ : X ≤ Λ) :
    ZLattice.covolume (E := E d) X =
      ZLattice.covolume (E := E d) Λ *
        (X.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
  classical
  have hdiv : ZLattice.covolume (E := E d) X / ZLattice.covolume (E := E d) Λ =
      (X.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
    exact ZLattice.covolume_div_covolume_eq_relIndex' X Λ hXΛ
  have hcΛ : ZLattice.covolume (E := E d) Λ ≠ 0 := ZLattice.covolume_ne_zero Λ
  calc
    ZLattice.covolume (E := E d) X
        = (ZLattice.covolume (E := E d) X / ZLattice.covolume (E := E d) Λ) *
            ZLattice.covolume (E := E d) Λ := by field_simp [hcΛ]
    _ = (X.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) *
          ZLattice.covolume (E := E d) Λ := by rw [hdiv]
    _ = ZLattice.covolume (E := E d) Λ *
          (X.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by ring

/-- A full-rank subgroup `X ≤ Λ` has finite index in `Λ` (`relIndex ≠ 0`). -/
lemma relIndex_ne_zero_of_fullRank {d : ℕ} (Λ X : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] [DiscreteTopology X] [IsZLattice ℝ X]
    (hXΛ : X ≤ Λ) : X.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 := by
  classical
  have hdiv : ZLattice.covolume (E := E d) X / ZLattice.covolume (E := E d) Λ =
      (X.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
    exact ZLattice.covolume_div_covolume_eq_relIndex' X Λ hXΛ
  have hdivpos : 0 < ZLattice.covolume (E := E d) X / ZLattice.covolume (E := E d) Λ := by
    exact div_pos (ZLattice.covolume_pos X) (ZLattice.covolume_pos Λ)
  have hri : 0 < (X.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
    rwa [hdiv] at hdivpos
  exact_mod_cast (ne_of_gt hri)

/-- The intersection of two full-rank subgroups of `Λ` has finite index in `Λ`. -/
lemma relIndex_inf_ne_zero_of_fullRank {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] [DiscreteTopology V] [IsZLattice ℝ V]
    [DiscreteTopology W] [IsZLattice ℝ W] (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) :
    (V ⊓ W).toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 := by
  have hV := relIndex_ne_zero_of_fullRank Λ V hVΛ
  have hW := relIndex_ne_zero_of_fullRank Λ W hWΛ
  -- identify (V ⊓ W).toAddSubgroup with V.toAddSubgroup ⊓ W.toAddSubgroup
  have hids : (V ⊓ W).toAddSubgroup = V.toAddSubgroup ⊓ W.toAddSubgroup := by
    ext x; rfl
  rw [hids]
  exact AddSubgroup.relIndex_inf_ne_zero hV hW

/-- Additive nsmul equals real scaling for natural coefficients. -/
lemma nsmul_eq_smul {d : ℕ} {x : E d} {n : ℕ} : n • x = (n : ℝ) • x := by
  exact (Nat.cast_smul_eq_nsmul ℝ n x).symm

/-- The real span of the intersection of two full-rank subgroups of a full-rank lattice
`Λ` is the whole space (the finite-index annihilator argument: `(V ⊓ W)` has finite
index in `Λ`, so for each `ℤ`-basis vector `bᵢ` of `Λ` some positive multiple
`nᵢ·bᵢ ∈ V ⊓ W`; those multiples form an `ℝ`-basis, hence span the whole space). -/
lemma realSpan_inf_eq_top {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    [DiscreteTopology V] [IsZLattice ℝ V] [DiscreteTopology W] [IsZLattice ℝ W]
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) :
    realSpan (V ⊓ W) = ⊤ := by
  classical
  let b : Fin d → E d := latticeZBasisE (d := d) Λ hΛfin
  have hrel : (V ⊓ W).toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 :=
    relIndex_inf_ne_zero_of_fullRank Λ V W hVΛ hWΛ
  -- per-index annihilator: some positive multiple of each lattice-basis vector lies in V ⊓ W
  have hmem_ann : ∀ i : Fin d, ∃ n : ℕ, 0 < n ∧ n • b i ∈ (V ⊓ W : Set (E d)) := by
    intro i
    dsimp [b]
    rcases AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hrel
      (latticeZBasisE_mem Λ hΛfin i) with ⟨n, hnpos, _hnle, hmem⟩
    refine ⟨n, hnpos, ?_⟩
    simpa using hmem.1
  choose n hn using hmem_ann
  let f : Fin d → E d := fun i => (n i : ℝ) • b i
  have hfmem : ∀ i : Fin d, f i ∈ (V ⊓ W : Set (E d)) := by
    intro i
    have h := (hn i).2
    simpa [f, nsmul_eq_smul] using h
  have hfLI : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hbLI : LinearIndependent ℝ b := latticeZBasisE_linearIndependent_real Λ hΛfin
    have hrel' : (∑ i : Fin d, (c i * (n i : ℝ)) • b i) = 0 := by
      have hc' : (∑ i : Fin d, c i • ((n i : ℝ) • b i)) = 0 := by simpa [f] using hc
      simpa [smul_smul, mul_assoc] using hc'
    have hc0 : ∀ i : Fin d, c i * (n i : ℝ) = 0 :=
      (Fintype.linearIndependent_iff.mp hbLI) (fun i => c i * (n i : ℝ)) hrel'
    intro i
    have hnne : (n i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hn i).1)
    exact mul_eq_zero.mp (hc0 i) |>.resolve_right hnne
  have hspan_top : Submodule.span ℝ (Set.range f) = ⊤ := by
    have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range f)) = d := by
      rw [finrank_span_eq_card (R := ℝ) hfLI]
      simp
    have hE : Module.finrank ℝ (E d) = d := by
      have hb' := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      simpa using (hb'.finrank_eq (Fin d))
    exact Submodule.eq_top_of_finrank_eq (by simpa [hE] using hfin)
  have hinc : Submodule.span ℝ (Set.range f) ≤ realSpan (V ⊓ W) := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span (hfmem i)
  exact le_antisymm (by simp [realSpan]) (by simpa [hspan_top] using hinc)

/-- The join of two full-rank subgroups is full-rank. -/
lemma realSpan_sup_eq_top {d : ℕ} (V W : Submodule ℤ (E d)) (hVdim : subDim V = d) :
    realSpan (V ⊔ W) = ⊤ := by
  have hmono : realSpan V ≤ realSpan (V ⊔ W) := by
    apply Submodule.span_mono
    intro x hx
    exact (le_sup_left : V ≤ V ⊔ W) hx
  have hVtop : realSpan V = ⊤ := realSpan_eq_top_of_subDim V hVdim
  apply le_antisymm
  · exact le_top
  · simpa [hVtop] using hmono



/-! ## 3. The ambient covolume product identity for full-rank subgroups -/

/-- The `AddSubgroup` of an inf of submodules is the inf of the `AddSubgroup`s. -/
lemma toAddSubgroup_inf {d : ℕ} (V W : Submodule ℤ (E d)) :
    (V ⊓ W).toAddSubgroup = V.toAddSubgroup ⊓ W.toAddSubgroup := by
  ext x; rfl

/-- The `AddSubgroup` of a sup of submodules is the sup of the `AddSubgroup`s. -/
lemma toAddSubgroup_sup {d : ℕ} (V W : Submodule ℤ (E d)) :
    (V ⊔ W).toAddSubgroup = V.toAddSubgroup ⊔ W.toAddSubgroup := by
  ext x
  constructor
  · intro hx
    change x ∈ (V ⊔ W : Submodule ℤ (E d)) at hx
    rw [Submodule.mem_sup] at hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    exact AddSubgroup.mem_sup.mpr ⟨a, ha, b, hb, rfl⟩
  · intro hx
    rw [AddSubgroup.mem_sup] at hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    change a + b ∈ (V ⊔ W : Submodule ℤ (E d))
    rw [Submodule.mem_sup]
    exact ⟨a, ha, b, hb, rfl⟩

/-- **Covolume product identity (full-rank ambient form)**: for two full-rank subgroups
`V, W ≤ Λ` of a full-rank lattice `Λ ≤ ℝᵈ`, the product of the ambient covolumes of
`V` and `W` equals the product of the ambient covolumes of their intersection and join:

    `covol(V) · covol(W) = covol(V ⊓ W) · covol(V ⊔ W)`.

This is the exact, index-theoretic form of the covolume submodularity for full-rank
subgroups (paper Lemma 3 reduces to an equality in this case; the mixed-rank version
needs the quadratic rank term and the elementary-divisor development). -/
theorem covolume_mul_eq_inf_sup {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    [DiscreteTopology V] [DiscreteTopology W]
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hVdim : subDim V = d) (hWdim : subDim W = d) :
    ZLattice.covolume (E := E d) V * ZLattice.covolume (E := E d) W =
      ZLattice.covolume (E := E d) (V ⊓ W) * ZLattice.covolume (E := E d) (V ⊔ W) := by
  classical
  haveI : IsZLattice ℝ V := isZLattice_of_subDim V hVdim
  haveI : IsZLattice ℝ W := isZLattice_of_subDim W hWdim
  -- instances for the intersection and the join
  have hInfΛ : V ⊓ W ≤ Λ := le_trans inf_le_left hVΛ
  have hSupΛ : V ⊔ W ≤ Λ := sup_le hVΛ hWΛ
  haveI : DiscreteTopology (V ⊓ W : Submodule ℤ (E d)) :=
    discreteTopology_of_le Λ (V ⊓ W) hInfΛ
  haveI : DiscreteTopology (V ⊔ W : Submodule ℤ (E d)) :=
    discreteTopology_of_le Λ (V ⊔ W) hSupΛ
  have hInfSpan : realSpan (V ⊓ W) = ⊤ := realSpan_inf_eq_top Λ V W hΛfin hVΛ hWΛ
  have hSupSpan : realSpan (V ⊔ W) = ⊤ := realSpan_sup_eq_top V W hVdim
  haveI : IsZLattice ℝ (V ⊓ W : Submodule ℤ (E d)) := ⟨hInfSpan⟩
  haveI : IsZLattice ℝ (V ⊔ W : Submodule ℤ (E d)) := ⟨hSupSpan⟩
  -- each covolume is covol(Λ)·(relative index in Λ)
  have hVc := covol_eq_covol_lattice_mul_relIndex Λ V hVΛ
  have hWc := covol_eq_covol_lattice_mul_relIndex Λ W hWΛ
  have hInfC := covol_eq_covol_lattice_mul_relIndex Λ (V ⊓ W) hInfΛ
  have hSupC := covol_eq_covol_lattice_mul_relIndex Λ (V ⊔ W) hSupΛ
  -- index multiplicativity (group theory) in AddSubgroup form
  have hidx : V.toAddSubgroup.relIndex Λ.toAddSubgroup *
        W.toAddSubgroup.relIndex Λ.toAddSubgroup =
      (V ⊓ W).toAddSubgroup.relIndex Λ.toAddSubgroup *
        (V ⊔ W).toAddSubgroup.relIndex Λ.toAddSubgroup := by
    rw [toAddSubgroup_inf, toAddSubgroup_sup]
    exact relIndex_mul_eq_inf_sup V.toAddSubgroup W.toAddSubgroup Λ.toAddSubgroup hVΛ hWΛ
  have hidxR : (V.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) *
        (W.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) =
      (((V ⊓ W).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) *
        ((V ⊔ W).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ)) := by
    exact_mod_cast hidx
  -- assemble
  calc
    ZLattice.covolume (E := E d) V * ZLattice.covolume (E := E d) W
        = (ZLattice.covolume (E := E d) Λ *
            (V.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ)) *
            (ZLattice.covolume (E := E d) Λ *
              (W.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ)) := by rw [hVc, hWc]
    _ = ZLattice.covolume (E := E d) Λ * ZLattice.covolume (E := E d) Λ *
          ((V.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) *
            (W.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ)) := by ring
    _ = ZLattice.covolume (E := E d) Λ * ZLattice.covolume (E := E d) Λ *
          (((V ⊓ W).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) *
            ((V ⊔ W).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ)) := by rw [hidxR]
    _ = (ZLattice.covolume (E := E d) Λ *
            ((V ⊓ W).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ)) *
            (ZLattice.covolume (E := E d) Λ *
              ((V ⊔ W).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ)) := by ring
    _ = ZLattice.covolume (E := E d) (V ⊓ W) *
          ZLattice.covolume (E := E d) (V ⊔ W) := by rw [hInfC, hSupC]

/-- **Log-covol submodularity (full-rank, exact)**: for two full-rank subgroups
`V, W ≤ Λ` of a full-rank lattice `Λ`, the log-covolume of `V ⊓ W` plus that of `V ⊔ W`
equals the sum for `V` and `W` (the exact form of paper Lemma 3 in the full-rank case,
where the quadratic rank term vanishes and the inequality is an equality). -/
theorem log_covolume_add_eq_inf_sup {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    [DiscreteTopology V] [DiscreteTopology W]
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hVdim : subDim V = d) (hWdim : subDim W = d) :
    Real.log (ZLattice.covolume (E := E d) (V ⊓ W)) +
        Real.log (ZLattice.covolume (E := E d) (V ⊔ W)) =
      Real.log (ZLattice.covolume (E := E d) V) +
        Real.log (ZLattice.covolume (E := E d) W) := by
  classical
  have hmul := covolume_mul_eq_inf_sup (d := d) Λ V W hΛfin hVΛ hWΛ hVdim hWdim
  have hInfΛ : V ⊓ W ≤ Λ := le_trans inf_le_left hVΛ
  have hSupΛ : V ⊔ W ≤ Λ := sup_le hVΛ hWΛ
  haveI : DiscreteTopology (V ⊓ W : Submodule ℤ (E d)) := discreteTopology_of_le Λ (V ⊓ W) hInfΛ
  haveI : DiscreteTopology (V ⊔ W : Submodule ℤ (E d)) := discreteTopology_of_le Λ (V ⊔ W) hSupΛ
  haveI : IsZLattice ℝ V := isZLattice_of_subDim V hVdim
  haveI : IsZLattice ℝ W := isZLattice_of_subDim W hWdim
  have hInfSpan : realSpan (V ⊓ W) = ⊤ := realSpan_inf_eq_top Λ V W hΛfin hVΛ hWΛ
  have hSupSpan : realSpan (V ⊔ W) = ⊤ := realSpan_sup_eq_top V W hVdim
  haveI : IsZLattice ℝ (V ⊓ W : Submodule ℤ (E d)) := ⟨hInfSpan⟩
  haveI : IsZLattice ℝ (V ⊔ W : Submodule ℤ (E d)) := ⟨hSupSpan⟩
  have hlog : Real.log (ZLattice.covolume (E := E d) V * ZLattice.covolume (E := E d) W) =
      Real.log (ZLattice.covolume (E := E d) (V ⊓ W) *
        ZLattice.covolume (E := E d) (V ⊔ W)) := by rw [hmul]
  have hV0 : ZLattice.covolume (E := E d) V ≠ 0 := ZLattice.covolume_ne_zero V
  have hW0 : ZLattice.covolume (E := E d) W ≠ 0 := ZLattice.covolume_ne_zero W
  have hInf0 : ZLattice.covolume (E := E d) (V ⊓ W) ≠ 0 := ZLattice.covolume_ne_zero (V ⊓ W)
  have hSup0 : ZLattice.covolume (E := E d) (V ⊔ W) ≠ 0 := ZLattice.covolume_ne_zero (V ⊔ W)
  rw [Real.log_mul hV0 hW0, Real.log_mul hInf0 hSup0] at hlog
  exact hlog.symm

/-! ## 4. Intrinsic (`latticeCovol`) form — the Grayson-data vocabulary -/

open Submission.GraysonEndpoints

/-- **Intrinsic covolume product identity**: the ambient covolume identity restated in the
Grayson-data quantity `latticeCovol` (own-real-span covolume) — for full-rank
`V, W ≤ Λ`, `latticeCovol (V ⊓ W) · latticeCovol (V ⊔ W) = latticeCovol V · latticeCovol W`,
since all four real spans are the whole space. -/
lemma latticeCovol_mul_eq_inf_sup {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    [DiscreteTopology V] [DiscreteTopology W]
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hVdim : subDim V = d) (hWdim : subDim W = d) :
    latticeCovol (V ⊓ W) * latticeCovol (V ⊔ W) = latticeCovol V * latticeCovol W := by
  classical
  have hAmb := covolume_mul_eq_inf_sup (d := d) Λ V W hΛfin hVΛ hWΛ hVdim hWdim
  have hInfΛ : V ⊓ W ≤ Λ := le_trans inf_le_left hVΛ
  have hSupΛ : V ⊔ W ≤ Λ := sup_le hVΛ hWΛ
  haveI : DiscreteTopology (V ⊓ W : Submodule ℤ (E d)) := discreteTopology_of_le Λ (V ⊓ W) hInfΛ
  haveI : DiscreteTopology (V ⊔ W : Submodule ℤ (E d)) := discreteTopology_of_le Λ (V ⊔ W) hSupΛ
  haveI : IsZLattice ℝ V := isZLattice_of_subDim V hVdim
  haveI : IsZLattice ℝ W := isZLattice_of_subDim W hWdim
  have hInfSpan : realSpan (V ⊓ W) = ⊤ := realSpan_inf_eq_top Λ V W hΛfin hVΛ hWΛ
  have hSupSpan : realSpan (V ⊔ W) = ⊤ := realSpan_sup_eq_top V W hVdim
  haveI : IsZLattice ℝ (V ⊓ W : Submodule ℤ (E d)) := ⟨hInfSpan⟩
  haveI : IsZLattice ℝ (V ⊔ W : Submodule ℤ (E d)) := ⟨hSupSpan⟩
  have hVc : latticeCovol V = ZLattice.covolume (E := E d) V :=
    latticeCovol_eq_covolume_of_span_top V (realSpan_eq_top_of_subDim V hVdim)
  have hWc : latticeCovol W = ZLattice.covolume (E := E d) W :=
    latticeCovol_eq_covolume_of_span_top W (realSpan_eq_top_of_subDim W hWdim)
  have hInfC : latticeCovol (V ⊓ W) = ZLattice.covolume (E := E d) (V ⊓ W) :=
    latticeCovol_eq_covolume_of_span_top (V ⊓ W) hInfSpan
  have hSupC : latticeCovol (V ⊔ W) = ZLattice.covolume (E := E d) (V ⊔ W) :=
    latticeCovol_eq_covolume_of_span_top (V ⊔ W) hSupSpan
  calc
    latticeCovol (V ⊓ W) * latticeCovol (V ⊔ W)
        = ZLattice.covolume (E := E d) (V ⊓ W) * ZLattice.covolume (E := E d) (V ⊔ W) := by
            rw [hInfC, hSupC]
    _ = ZLattice.covolume (E := E d) V * ZLattice.covolume (E := E d) W := hAmb.symm
    _ = latticeCovol V * latticeCovol W := by rw [hVc, hWc]

/-- **Intrinsic log-covol submodularity (full-rank, exact)**: the exact form of paper
Lemma 3 in the Grayson-data quantity over full-rank subgroups:
`log covol(V ⊓ W) + log covol(V ⊔ W) = log covol V + log covol W`. -/
lemma log_latticeCovol_add_eq_inf_sup {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    [DiscreteTopology V] [DiscreteTopology W]
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hVdim : subDim V = d) (hWdim : subDim W = d) :
    Real.log (latticeCovol (V ⊓ W)) + Real.log (latticeCovol (V ⊔ W)) =
      Real.log (latticeCovol V) + Real.log (latticeCovol W) := by
  classical
  have hmul := latticeCovol_mul_eq_inf_sup Λ V W hΛfin hVΛ hWΛ hVdim hWdim
  have hInfΛ : V ⊓ W ≤ Λ := le_trans inf_le_left hVΛ
  have hSupΛ : V ⊔ W ≤ Λ := sup_le hVΛ hWΛ
  haveI : DiscreteTopology (V ⊓ W : Submodule ℤ (E d)) := discreteTopology_of_le Λ (V ⊓ W) hInfΛ
  haveI : DiscreteTopology (V ⊔ W : Submodule ℤ (E d)) := discreteTopology_of_le Λ (V ⊔ W) hSupΛ
  haveI : IsZLattice ℝ V := isZLattice_of_subDim V hVdim
  haveI : IsZLattice ℝ W := isZLattice_of_subDim W hWdim
  have hInfSpan : realSpan (V ⊓ W) = ⊤ := realSpan_inf_eq_top Λ V W hΛfin hVΛ hWΛ
  have hSupSpan : realSpan (V ⊔ W) = ⊤ := realSpan_sup_eq_top V W hVdim
  haveI : IsZLattice ℝ (V ⊓ W : Submodule ℤ (E d)) := ⟨hInfSpan⟩
  haveI : IsZLattice ℝ (V ⊔ W : Submodule ℤ (E d)) := ⟨hSupSpan⟩
  -- positivity of the ambient covolumes ⟹ positivity of the intrinsic covolumes
  have hpos (X : Submodule ℤ (E d)) [DiscreteTopology X] [IsZLattice ℝ X]
      (hXsp : Submodule.span ℝ (X : Set (E d)) = ⊤) :
      0 < latticeCovol X := by
    rw [latticeCovol_eq_covolume_of_span_top X hXsp]
    exact ZLattice.covolume_pos X
  have hVpos := hpos V (realSpan_eq_top_of_subDim V hVdim)
  have hWpos := hpos W (realSpan_eq_top_of_subDim W hWdim)
  have hInfpos := hpos (V ⊓ W) hInfSpan
  have hSuppos := hpos (V ⊔ W) hSupSpan
  have hlog : Real.log (latticeCovol V * latticeCovol W) =
      Real.log (latticeCovol (V ⊓ W) * latticeCovol (V ⊔ W)) := by rw [hmul]
  rw [Real.log_mul (ne_of_gt hVpos) (ne_of_gt hWpos),
      Real.log_mul (ne_of_gt hInfpos) (ne_of_gt hSuppos)] at hlog
  exact hlog.symm


end Submission.Submodularity

end
