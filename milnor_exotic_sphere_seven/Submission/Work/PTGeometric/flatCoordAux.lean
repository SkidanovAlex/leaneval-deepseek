import Submission.Work.PTGeometric.blockPt
import Submission.Work.PTGeometric.SourceNull
import Submission.Work.PTGeometric.genLoopListConcat_eq_basepoint_of_wall
import Submission.Work.PTGeometric.PadAmb

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: auxiliary lemmas for the smoothness of the coordinate field on the collar

The flat source homotopy's coordinate field is smooth on the collar `{x 0 < 1/2}` because there it is
the explicit concatenation `alphaFamily` of the pieces' collapse loops read at the cube coordinates
of the source, and on each dyadic block of the cube the concatenation is TUBULAR's tube collapse,
whose ambient coordinates (`tubeNormalProj`, `tubeNormalCoord`) are `C^∞`.

This file collects the analytic and reindexing lemmas that the argument consumes:

* `Work.PTGeometric.finKRInv` and its two round-trip identities — the reindexing between the
  concatenation cube `Fin (k+8)` and the cube `Fin (8+k)` of TUBULAR;
* the smoothness of the cube coordinates `cubeCoord` (`Work.PTGeometric.contMDiff_cubeCoord_pi`) and
  of their composite with the source coordinates (`Work.PTGeometric.contMDiff_collComp`);
* the affine map `Work.PTGeometric.eucOfReal` from real coordinates to `ℝ^N` realising
  `cubeToEuc`, with its smoothness and its component formula;
* the tube chain: `alphaV` outside the open tube is the base point
  (`Work.PTGeometric.alphaV_eq_basepoint_of_notMem_openTube`), the open tube is recovered from the
  non-vanishing of `alphaV` (`Work.PTGeometric.mem_openTube_of_alphaV_ne`), and the ambient
  coordinates of the collapse inside the tube are TUBULAR's
  (`Work.PTGeometric.coord_collapse_of_isGeom`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

/-! ## The reindexing `Fin (k+8) → Fin (8+k)` and its inverse -/

/-- The inverse of the reindexing `Work.PTGeometric.finKR`. -/
def finKRInv (k : ℕ) : Fin (8 + k) → Fin (k + 8) := Fin.cast (Nat.add_comm 8 k)

theorem finKRInv_finKR (k : ℕ) (j : Fin (k + 8)) : finKRInv k (finKR k j) = j := by
  rw [finKRInv, finKR, Fin.cast_cast]
  exact Fin.cast_eq_self j

theorem finKR_finKRInv (k : ℕ) (l : Fin (8 + k)) : finKR k (finKRInv k l) = l := by
  rw [finKRInv, finKR, Fin.cast_cast]
  exact Fin.cast_eq_self l

/-! ## The smoothness of the cube coordinates -/

theorem contMDiff_cubeCoord_apply (n : ℕ) (m : Fin n) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞
      (fun y => ((cubeCoord n y m : Set.Icc (0 : ℝ) 1) : ℝ)) := by
  rw [contMDiff_iff_contDiff]
  have h1 : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => y m) :=
    (ContinuousLinearMap.proj m |>.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toContinuousLinearMap).contDiff
  have h2 : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + (y m) ^ 2) :=
    contDiff_const.add (h1.pow 2)
  have h3 : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => Real.sqrt (1 + (y m) ^ 2)) :=
    ContDiff.sqrt h2 (fun y => by positivity)
  have h4 : ContDiff ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin n) => (1 + y m / Real.sqrt (1 + (y m) ^ 2)) / 2) :=
    (contDiff_const.add (h1.div h3 (fun y => by positivity))).div_const 2
  simpa only [cubeCoord_apply_coe] using h4

theorem contMDiff_cubeCoord_pi (n : ℕ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun y => fun m => ((cubeCoord n y m : Set.Icc (0 : ℝ) 1) : ℝ)) := by
  rw [contMDiff_pi_space]
  exact fun m => contMDiff_cubeCoord_apply n m

/-- The cube coordinates of the collar of the flat source, as smooth functions of the source
coordinate. -/
theorem contMDiff_collComp (k : ℕ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin ((8 + k) + 1))) 𝓘(ℝ, Fin (k + 8) → ℝ) ∞
      (fun y => fun m =>
        ((cubeCoord (k + 8) (tail (k + 8) (srcCast k y)) m : Set.Icc (0 : ℝ) 1) : ℝ)) :=
  (contMDiff_cubeCoord_pi (k + 8)).comp
    (((tailCLM (k + 8)).comp (srcCast k)).contMDiff)

/-- The collar cube point itself. -/
def collPt (k : ℕ) (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    Fin (k + 8) → Set.Icc (0 : ℝ) 1 :=
  cubeCoord (k + 8) (tail (k + 8) (srcCast k y))

@[simp] theorem collPt_apply (k : ℕ) (y : EuclideanSpace ℝ (Fin ((8 + k) + 1)))
    (m : Fin (k + 8)) :
    ((collPt k y m : Set.Icc (0 : ℝ) 1) : ℝ)
      = ((cubeCoord (k + 8) (tail (k + 8) (srcCast k y)) m : Set.Icc (0 : ℝ) 1) : ℝ) := rfl

/-! ## The affine realisation of the cube of radius `R` -/

/-- **The cube of radius `R` on real coordinates**: `(2R (v_i - 1/2))_i`.  It is the affine map
which, on the unit cube, is TUBULAR's `cubeToEuc`. -/
def eucOfReal (N : ℕ) (R : ℝ) (v : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) :=
  Work.Tubular.funToEuc N (fun i => 2 * R * (v i - 1 / 2))

theorem eucOfReal_apply (N : ℕ) (R : ℝ) (v : Fin N → ℝ) (i : Fin N) :
    eucOfReal N R v i = 2 * R * (v i - 1 / 2) := by
  simp [eucOfReal, Work.Tubular.funToEuc]

theorem contMDiff_eucOfReal (N : ℕ) (R : ℝ) :
    ContMDiff 𝓘(ℝ, Fin N → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (eucOfReal N R) := by
  rw [contMDiff_iff_contDiff]
  exact (Work.Tubular.funToEuc N).contDiff.comp (by fun_prop)

theorem eucOfReal_coll (N : ℕ) (R : ℝ) (t : Fin N → Set.Icc (0 : ℝ) 1) :
    eucOfReal N R (fun i => ((t i : Set.Icc (0 : ℝ) 1) : ℝ))
      = Work.Tubular.cubeToEuc N R t := by
  rw [eucOfReal, Work.Tubular.cubeToEuc_apply]
  rfl

/-- A cube point of `Fin (8+k)` read through the reindexing `finKR`. -/
def reIdx (k : ℕ) (s : Fin (k + 8) → Set.Icc (0 : ℝ) 1) :
    Fin (8 + k) → Set.Icc (0 : ℝ) 1 := fun l => s (finKRInv k l)

@[simp] theorem reIdx_apply (k : ℕ) (s : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
    (l : Fin (8 + k)) : reIdx k s l = s (finKRInv k l) := rfl

theorem reIdx_comp_finKR (k : ℕ) (s : Fin (k + 8) → Set.Icc (0 : ℝ) 1) :
    (fun j => reIdx k s (finKR k j)) = s := by
  funext j
  rw [reIdx_apply, finKRInv_finKR]

/-! ## The tube chain -/

section Tube

variable {V : Man8} {k : ℕ} {E : EmbeddingData V (8 + k)} {ε : ℝ}

/-- **Outside the open tube the collapse is the base point.** -/
theorem alphaV_eq_basepoint_of_notMem_openTube (C : Work.Tubular.TubeChart E ε)
    {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    {Y : Type} [TopologicalSpace Y] (y₀ : Y)
    (J : C(OnePoint (Work.Tubular.NormalTotal E), Y)) (hJ : J OnePoint.infty = y₀)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {t : Fin (8 + k) → Set.Icc (0 : ℝ) 1}
    (ht : Work.Tubular.cubeToEuc (8 + k) R t ∉ C.openTube) :
    Work.Tubular.alphaV C hR hbox y₀ J hJ g hg t = y₀ := by
  show J (Work.Tubular.tubeCollapseCubeOnePoint g R t) = y₀
  rw [Work.Tubular.tubeCollapseCubeOnePoint_apply, hg _ ht, hJ]

/-- **The open tube is recovered from the non-vanishing of the collapse.** -/
theorem mem_openTube_of_alphaV_ne (C : Work.Tubular.TubeChart E ε)
    {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    {Y : Type} [TopologicalSpace Y] (y₀ : Y)
    (J : C(OnePoint (Work.Tubular.NormalTotal E), Y)) (hJ : J OnePoint.infty = y₀)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {t : Fin (8 + k) → Set.Icc (0 : ℝ) 1}
    (h : Work.Tubular.alphaV C hR hbox y₀ J hJ g hg t ≠ y₀) :
    Work.Tubular.cubeToEuc (8 + k) R t ∈ C.openTube :=
  by_contra fun hc => h (alphaV_eq_basepoint_of_notMem_openTube C hR hbox y₀ J hJ g hg hc)

end Tube

/-- **The ambient coordinates of the genuine collapse, on the open tube.**  The loop of the
Pontryagin–Thom representative of a piece is TUBULAR's concrete collapse (`GenuineTubeGeometry.isGeom`),
so its coordinate reading is TUBULAR's tube data (`GenuineTubeGeometry.coord_collapse`). -/
theorem coord_collapse_of_isGeom {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} (G : GenuineTubeGeometry k D ι Fam) (i : ι)
    (s : Fin (8 + k) → Set.Icc (0 : ℝ) 1)
    (hs : Work.Tubular.cubeToEuc (8 + k) G.R s ∈ (G.chart i).openTube)
    (h : (G.rep i).collapse (fun j => s (finKR k j)) ≠ D.t₀) :
    G.coord ⟨(G.rep i).collapse (fun j => s (finKR k j)), h⟩ =
      (padEndEuc k G.mU G.hmU (tubeNormalProj (G.emb i) (G.chart i)
          (Work.Tubular.cubeToEuc (8 + k) G.R s)),
       padEuc k G.mU G.hmU (tubeNormalCoord (G.emb i) (G.chart i)
          (Work.Tubular.cubeToEuc (8 + k) G.R s))) := by
  obtain ⟨hne, heq⟩ := G.coord_collapse i s hs
  have hiso := G.isGeom i s
  have key : (⟨(G.rep i).collapse (fun j => s (finKR k j)), h⟩ : {x : D.T // x ≠ D.t₀})
      = ⟨Work.Tubular.alphaV (G.chart i) G.hR (G.hbox i) D.t₀ (G.J i) (G.hJ i) (G.g i) (G.hg i) s,
          hne⟩ :=
    Subtype.ext hiso
  rw [key, heq]

/-! ## Two elementary facts about loops and lists -/

theorem genLoop_const_apply {N : Type*} {X : Type} [TopologicalSpace X] {x : X}
    (t : N → Set.Icc (0 : ℝ) 1) :
    (GenLoop.const : GenLoop N X x) t = x := rfl

theorem get_ofFn_eq {n : ℕ} {α : Type*} (f : Fin n → α) (i : ℕ)
    (h : i < (List.ofFn f).length) :
    (List.ofFn f)[i] = f ⟨i, by rwa [List.length_ofFn] at h⟩ := by
  have h' : i < n := by rwa [List.length_ofFn] at h
  have := List.get_ofFn f ⟨i, by rw [List.length_ofFn]; exact h'⟩
  simpa using this

/-- The components of the collar cube point are smooth functions of the source coordinate. -/
theorem contMDiff_collPt_apply (k : ℕ) (m : Fin (k + 8)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin ((8 + k) + 1))) 𝓘(ℝ, ℝ) ∞
      (fun y => ((collPt k y m : Set.Icc (0 : ℝ) 1) : ℝ)) :=
  (contMDiff_pi_space.mp (contMDiff_collComp k)) m

/-- **The extraction of the block index**: off the "wall" of the cube, a cube point lies in the
*open* `k`-th dyadic block for a unique `k < n`. -/
theorem existsUnique_block_index {ξ : ℝ} {n : ℕ} (h1 : ξ ≤ 1) (hn : 1 < (2 : ℝ) ^ n * ξ)
    (hdy : ∀ c < n, (2 : ℝ) ^ c * ξ ≠ 1) :
    ∃! k : ℕ, k < n ∧ 1 < (2 : ℝ) ^ (k + 1) * ξ ∧ (2 : ℝ) ^ k * ξ < 1 := by
  set B : Set ℕ := {d | 1 < (2 : ℝ) ^ d * ξ} with hB
  have hne : B.Nonempty := ⟨n, hn⟩
  set d := Nat.find hne with hd
  have hmin : 1 < (2 : ℝ) ^ d * ξ := Nat.find_spec hne
  have hle : d ≤ n := Nat.find_min' hne hn
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h] at hmin; norm_num at hmin; linarith
    · exact h
  have hk : d - 1 < n := by omega
  have hlo : 1 < (2 : ℝ) ^ ((d - 1) + 1) * ξ := by
    rw [show d - 1 + 1 = d by omega]; exact hmin
  have hhi : (2 : ℝ) ^ (d - 1) * ξ < 1 := by
    have hnot : ¬ (1 < (2 : ℝ) ^ (d - 1) * ξ) := Nat.find_min hne (by omega : d - 1 < d)
    have hle2 : (2 : ℝ) ^ (d - 1) * ξ ≤ 1 := not_lt.mp hnot
    have hne1 : (2 : ℝ) ^ (d - 1) * ξ ≠ 1 := hdy (d - 1) (by omega)
    exact lt_of_le_of_ne hle2 hne1
  refine ⟨d - 1, ⟨hk, hlo, hhi⟩, ?_⟩
  rintro k ⟨hk', hlo', hhi'⟩
  have hpos : 0 < ξ := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
    have h3 : (0 : ℝ) < ξ * (2 : ℝ) ^ (k + 1) := by
      rw [mul_comm]; linarith
    exact pos_of_mul_pos_left h3 h2.le
  have hkey : k + 1 = d := by
    rcases lt_trichotomy (k + 1) d with h | h | h
    · exfalso
      have h4 := Nat.find_min' hne hlo'
      omega
    · exact h
    · exfalso
      have hdk : d ≤ k := by omega
      have h2 : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hdk
      have h3 : (2 : ℝ) ^ d * ξ ≤ (2 : ℝ) ^ k * ξ := mul_le_mul_of_nonneg_right h2 hpos.le
      linarith
  omega

/-- **The block index of a cube point whose value is not the base point.**  This is the combination
of the wall lemma with the arithmetic extraction: off the walls, the cube point lies in the *open*
`k`-th dyadic block for a unique `k < l.length`. -/
theorem exists_block_interval {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (l : List (GenLoop N X x)) (t : N → Set.Icc (0 : ℝ) 1)
    (hy : genLoopListConcat i l t ≠ x) :
    ∃ k : ℕ, k < l.length ∧ 1 < (2 : ℝ) ^ (k + 1) * (t i : ℝ) ∧
      (2 : ℝ) ^ k * (t i : ℝ) < 1 := by
  have hwall : ¬ ((2 : ℝ) ^ l.length * (t i : ℝ) ≤ 1 ∨
      ∃ c < l.length, (2 : ℝ) ^ c * (t i : ℝ) = 1) := by
    intro hh
    exact hy (genLoopListConcat_eq_basepoint_of_wall i l t hh)
  have h1 : (t i : ℝ) ≤ 1 := (t i).2.2
  have hn : 1 < (2 : ℝ) ^ l.length * (t i : ℝ) := lt_of_not_ge (fun hh => hwall (Or.inl hh))
  have hdy : ∀ c < l.length, (2 : ℝ) ^ c * (t i : ℝ) ≠ 1 :=
    fun c hc hh => hwall (Or.inr ⟨c, hc, hh⟩)
  obtain ⟨k, hk, -⟩ := existsUnique_block_index h1 hn hdy
  exact ⟨k, hk.1, hk.2.1, hk.2.2⟩

end

end Work.PTGeometric
