/-
  WilC4 / `crit_def_bnd`.

  Let `Y ⊆ ℝ^{k+2}` be a `∅`-definable family and let

  * `BndDom Y = {v : ℝ^{k+1} | IsBnd (DomFib Y (tup v)) (v 0)}`,
  * `BndZero Y = {v : ℝ^{k+1} | IsBnd (ZeroFib Y (tup v)) (v 0)}`

  be the families of topological boundary points (`Work.WilC2.IsBnd`) of the domain and of the
  zero set of the fibre.  This file proves that both families are `∅`-definable and that each of
  their fibres is finite (for every parameter tuple `c`, the set of `x` with
  `Fin.cons x c ∈ BndDom Y`, resp. `∈ BndZero Y`, is finite).

  Proof.  The family is decomposed as follows.

  * `PDom Y = {p | ∃ y, Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y}` (`Work.WilC4.PDom`) is the
    domain family; `Pfib1 (PDom Y) p = DomFib Y (tup p)` (`cdb_Pfib1_PDom`), and `PDom Y` is
    `∅`-definable (`cdb_paramDom`, via the pulling back of `Y` along `Pτ` and one projection).
  * `ZS Y = {q | Fin.cons (q 0) (Fin.cons 0 (Fin.tail q)) ∈ Y}` is the `y = 0` slice family;
    `Pfib1 (ZS Y) p = ZeroFib Y (tup p)` (`cdb_Pfib1_ZS`), and `ZS Y` is `∅`-definable
    (`cdb_ZS`).
  * The parametric topological boundary `p ↦ IsBnd (Pfib1 S p) (p 0)` of a `∅`-definable family
    `S` is `∅`-definable; this is the colleague's lemma
    `Work.WilC4.cdbPieces.paramBnd_slice` (the parametric form of `WilC2.bnd_definable_alt`).
  * Finite fibres: `DomFib Y c` and `ZeroFib Y c` are `∅`-definable
    (`cdb_DomFib`, `cdb_ZeroFib`: the fibre at the fixed parameter tuple `c` is the preimage of
    `PDom Y`, resp. `ZS Y`, under the `∅`-definable map `v ↦ Fin.cons (v 0) c`), so their
    boundary sets are finite by o-minimality (`Work.WilC4.bnd_finite_of_definable`, the
    o-minimality consequence of `hOM`).
-/
import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC4.mono_real
import Submission.Work.WilC4.cdbPieces.paramBnd_slice

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ### 1. `∅`-definable constant functions -/

theorem empty_definableFun_const {α : Type} (r : ℝ) :
    (∅ : Set ℝ).DefinableFun WilkiesDesign.CG.LRc (fun _ : α → ℝ => r) := by
  have h := empty_definable_coord_eq (α := Option α) Option.none r
  rw [Set.DefinableFun]
  convert h using 1
  ext v
  simp [Function.tupleGraph, eq_comm]

/-! ### 2. `PDom` is `∅`-definable -/

theorem cdb_paramDom {n : ℕ} {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PDom Y) := by
  have hPExt : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PExt Y) := by
    rw [PExt]
    exact hY.preimage_comp (Pτ n)
  have h := hPExt.exists_of_finite
  have hset : PDom Y =
      {v : Fin (n + 1) → ℝ | ∃ u : Fin 1 → ℝ, Sum.elim v u ∈ PExt Y} := by
    ext p
    simp only [Set.mem_ofPred_eq, PDom]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨fun _ => y, (PExt_apply p y).mpr hy⟩
    · rintro ⟨u, hu⟩
      have hu_eq : Sum.elim p u = Sum.elim p (fun _ : Fin 1 => u 0) := by
        funext s
        rcases s with i | j
        · rfl
        · exact congrArg u (Subsingleton.elim j 0)
      rw [hu_eq] at hu
      exact ⟨u 0, (PExt_apply p (u 0)).mp hu⟩
  rw [hset]
  exact h

/-! ### 3. The `y = 0` slice family -/

/-- The map sending a parameter tuple `q` to the tuple `(q 0, 0, q 1, …, q k)`. -/
def ZMap {k : ℕ} (q : Fin (k + 1) → ℝ) : Fin (k + 2) → ℝ :=
  Fin.cons (q 0) (Fin.cons 0 (Fin.tail q))

/-- The family obtained from `Y` by slicing the value coordinate at `0`. -/
def ZS {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) := ZMap ⁻¹' Y

theorem cdb_ZS {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (ZS Y) := by
  unfold ZS
  refine Set.Definable.preimage_map (F := ZMap) ?_ hY
  intro i
  refine Fin.cases (motive := fun i => (∅ : Set ℝ).DefinableFun WilkiesDesign.CG.LRc
      (fun q : Fin (k + 1) → ℝ => ZMap q i)) ?_ ?_ i
  · simpa only [ZMap, Fin.cons_zero] using
      (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ))
        (i := (0 : Fin (k + 1))))
  · intro j
    refine Fin.cases (motive := fun j => (∅ : Set ℝ).DefinableFun WilkiesDesign.CG.LRc
        (fun q : Fin (k + 1) → ℝ => ZMap q (Fin.succ j))) ?_ ?_ j
    · simpa only [ZMap, Fin.cons_succ, Fin.cons_zero] using
        (empty_definableFun_const (α := Fin (k + 1)) (0 : ℝ))
    · intro j'
      have h : (fun q : Fin (k + 1) → ℝ => ZMap q (Fin.succ (Fin.succ j'))) =
          (fun q => q (Fin.succ j')) := by
        funext q; rfl
      rw [h]
      exact Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ))
        (i := (Fin.succ j' : Fin (k + 1)))

/-! ### 4. Fibres at fixed parameters -/

theorem cdb_cons_fibre {k : ℕ} {B : Set (Fin (k + 1) → ℝ)}
    (hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B) (c : Fin k → ℝ) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {v : Fin 1 → ℝ | Fin.cons (v 0) c ∈ B} := by
  refine Set.Definable.preimage_map
    (F := fun v : Fin 1 → ℝ => (Fin.cons (v 0) c : Fin (k + 1) → ℝ)) ?_ hB
  intro i
  refine Fin.cases (motive := fun i => (∅ : Set ℝ).DefinableFun WilkiesDesign.CG.LRc
      (fun v : Fin 1 → ℝ => (Fin.cons (v 0) c : Fin (k + 1) → ℝ) i)) ?_ ?_ i
  · simpa only [Fin.cons_zero] using
      (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set ℝ)) (i := (0 : Fin 1)))
  · intro j
    have h : (fun v : Fin 1 → ℝ => (Fin.cons (v 0) c : Fin (k + 1) → ℝ) (Fin.succ j)) =
        (fun _ : Fin 1 → ℝ => c j) := by
      funext v; rw [Fin.cons_succ]
    rw [h]
    exact empty_definableFun_const (α := Fin 1) (c j)

theorem cdb_DomFib {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) (c : Fin k → ℝ) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (DomFib Y c) := by
  show (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {v : Fin 1 → ℝ | v 0 ∈ DomFib Y c}
  have hset : {v : Fin 1 → ℝ | v 0 ∈ DomFib Y c} =
      {v : Fin 1 → ℝ | Fin.cons (v 0) c ∈ PDom Y} := by
    ext v
    simp only [Set.mem_ofPred_eq, DomFib, CGr, PDom]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by simpa only [Fin.cons_zero, Fin.tail_cons] using hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by simpa only [Fin.cons_zero, Fin.tail_cons] using hy⟩
  rw [hset]
  exact cdb_cons_fibre (B := PDom Y) (cdb_paramDom hY) c

theorem cdb_ZeroFib {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) (c : Fin k → ℝ) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (ZeroFib Y c) := by
  show (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {v : Fin 1 → ℝ | v 0 ∈ ZeroFib Y c}
  have hset : {v : Fin 1 → ℝ | v 0 ∈ ZeroFib Y c} =
      {v : Fin 1 → ℝ | Fin.cons (v 0) c ∈ ZS Y} := by
    ext v
    simp only [Set.mem_ofPred_eq, ZeroFib, CGr, ZS, ZMap, Set.mem_preimage]
    constructor
    · intro hh
      simpa only [Fin.cons_zero, Fin.tail_cons] using hh
    · intro hh
      simpa only [Fin.cons_zero, Fin.tail_cons] using hh
  rw [hset]
  exact cdb_cons_fibre (B := ZS Y) (cdb_ZS hY) c

/-! ### 5. Identifications of `BndDom`, `BndZero` with the parametric boundary families -/

theorem cdb_Pfib1_PDom {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (p : Fin (k + 1) → ℝ) :
    Pfib1 (PDom Y) p = DomFib Y (tup p) := by
  have ht : tup p = Fin.tail p := rfl
  rw [ht]
  ext x
  simp only [Pfib1, PDom, DomFib, CGr, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa only [Fin.cons_zero, Fin.tail_cons] using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa only [Fin.cons_zero, Fin.tail_cons] using hy⟩

theorem cdb_Pfib1_ZS {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (p : Fin (k + 1) → ℝ) :
    Pfib1 (ZS Y) p = ZeroFib Y (tup p) := by
  have ht : tup p = Fin.tail p := rfl
  rw [ht]
  ext x
  simp only [Pfib1, ZS, ZMap, ZeroFib, CGr, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · intro hh
    simpa only [Fin.cons_zero, Fin.tail_cons] using hh
  · intro hh
    simpa only [Fin.cons_zero, Fin.tail_cons] using hh

theorem cdb_bndDom_eq {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) :
    BndDom Y = {p : Fin (k + 1) → ℝ | WilC2.IsBnd (Pfib1 (PDom Y) p) (p 0)} := by
  ext p
  simp only [BndDom, Set.mem_ofPred_eq]
  rw [cdb_Pfib1_PDom]

theorem cdb_bndZero_eq {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) :
    BndZero Y = {p : Fin (k + 1) → ℝ | WilC2.IsBnd (Pfib1 (ZS Y) p) (p 0)} := by
  ext p
  simp only [BndZero, Set.mem_ofPred_eq]
  rw [cdb_Pfib1_ZS]

/-! ### 6. The target -/

theorem crit_def_bnd {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) (hOM : WilkiesDesign.CG.OMinModels) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (BndDom Y) ∧
      (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (BndZero Y) ∧
      (∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ BndDom Y}.Finite ∧
        {x : ℝ | Fin.cons x c ∈ BndZero Y}.Finite) := by
  have hP := cdb_paramDom hY
  have hZ := cdb_ZS hY
  refine ⟨?_, ?_, ?_⟩
  · rw [cdb_bndDom_eq]
    exact cdbPieces.paramBnd_slice hP
  · rw [cdb_bndZero_eq]
    exact cdbPieces.paramBnd_slice hZ
  · intro c
    refine ⟨?_, ?_⟩
    · refine (bnd_finite_of_definable hOM (cdb_DomFib hY c)).subset ?_
      intro x hx
      simpa only [BndDom, Set.mem_ofPred_eq, tup_cons, Fin.cons_zero] using hx
    · refine (bnd_finite_of_definable hOM (cdb_ZeroFib hY c)).subset ?_
      intro x hx
      simpa only [BndZero, Set.mem_ofPred_eq, tup_cons, Fin.cons_zero] using hx

end Work.WilC4
