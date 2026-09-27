import Mathlib
import Submission.Work.EKLC6Core.CellsData
import Submission.Work.EKLC6Core.CellSysDefs
import Submission.Work.EKLC6Core.atom_MSig
import Submission.Work.EKLC6Core.V_estimates
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLComp.inv_mem_V

/-!
# `Work.EKLC6Core.cellsData_atom_facts`

The transfer of `Work.EKLC6Core.atom_MSig` / `shape_MSig_open` / `shape_MSig_uball`
from the `CellSys` structure to the *raw* cell data used by `Work.EKLC6Core.CellsData`.

For a raw cell family `Q` (pairwise disjoint open cells at scales `d`, each inside a
`V (d k / 2)`-ball around `mkX (g k)` on which the orbit map is injective on `V (4 d k)`) and a
countable family `O` of open sets whose `U`-saturations separate left `U`-cosets, the atoms of
the cut σ-algebra `MSigCut U Q d g O` at a free point `y` of a cell are the pieces of the
`U`-orbit of `y` cut out by the lifted ball of the cell:

* `atom (MSigCut U Q d g O) y ⊆ Q k`, and it is contained in the `U`-orbit of `y`;
* `shape (MSigCut U Q d g O) U y` is the trace on `U` of an open set;
* `shape (MSigCut U Q d g O) U y ⊆ Uball U (1 / 2)`.

The canonical lift of `y ∈ Q k` is the witness of `hsub k`; membership in a clipped cylinder
generator is membership of the lift in the saturation, and injectivity on `V (4 d k)` identifies
the two lifts.
-/

open MeasureTheory
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

/-! ## Raw cell data and its canonical lift -/

/-- The raw geometric input of the cut construction: cells `Q`, scales `d`, centres `g`, a
separating family `O` of open subsets of `SL₃(ℝ)`. -/
structure RawCells (U : Subgroup SL3) where
  /-- the cells -/
  Q : ℕ → Set X3
  /-- the cell scales -/
  d : ℕ → ℝ
  /-- the cell centres, as lifts -/
  g : ℕ → SL3
  /-- a countable family of open sets separating the left `U`-cosets -/
  O : ℕ → Set SL3
  hopen : ∀ k, IsOpen (Q k)
  hdisj : ∀ k l, k ≠ l → Disjoint (Q k) (Q l)
  hdpos : ∀ k, 0 < d k
  hdsmall : ∀ k, d k ≤ 1 / 16
  hsub : ∀ k, Q k ⊆ (fun v : SL3 => v • mkX (g k)) '' (V (d k / 2))
  hinj : ∀ k (v₁ v₂ : SL3), v₁ ∈ V (4 * d k) → v₂ ∈ V (4 * d k) →
    v₁ • mkX (g k) = v₂ • mkX (g k) → v₁ = v₂
  hOopen : ∀ m, IsOpen (O m)
  hOsep : ∀ z w : SL3, (∀ m, (z ∈ satUC U (O m) ↔ w ∈ satUC U (O m))) →
    w ∈ satUC U ({z} : Set SL3)

namespace RawCells

/-- The canonical lift of a point of a cell: the witness of `hsub k`, multiplied by the centre. -/
noncomputable def liftR {U : Subgroup SL3} (R : RawCells U) (k : ℕ) (y : X3) : SL3 := by
  classical
  exact if h : y ∈ R.Q k then Classical.choose (R.hsub k h) * R.g k else 1

end RawCells

variable {U : Subgroup SL3}

/-- The canonical lift of a point of a cell lies in the `V (d k / 2)`-ball. -/
theorem liftR_mem_half (R : RawCells U) (k : ℕ) {y : X3} (hy : y ∈ R.Q k) :
    R.liftR k y ∈ liftedC (R.d k / 2) (R.g k) := by
  classical
  obtain ⟨h1, -⟩ := Classical.choose_spec (R.hsub k hy)
  rw [RawCells.liftR, dif_pos hy]
  exact ⟨Classical.choose (R.hsub k hy), h1, rfl⟩

/-- The canonical lift of a point of a cell lies in the lifted ball of that cell. -/
theorem liftR_mem (R : RawCells U) (k : ℕ) {y : X3} (hy : y ∈ R.Q k) :
    R.liftR k y ∈ liftedC (R.d k) (R.g k) := by
  obtain ⟨w, hw, hwq⟩ := liftR_mem_half R k hy
  exact ⟨w, V_mono' (by linarith [R.hdpos k]) hw, hwq⟩

/-- The canonical lift of a point of a cell maps back to that point. -/
theorem liftR_mkX (R : RawCells U) (k : ℕ) {y : X3} (hy : y ∈ R.Q k) :
    mkX (R.liftR k y) = y := by
  classical
  have h2 := (Classical.choose_spec (R.hsub k hy)).2
  rw [RawCells.liftR, dif_pos hy]
  simpa only [atomMSig_smul_mkX] using h2

/-- `mkX` is injective on a lifted ball. -/
theorem mkX_inj_liftedR (R : RawCells U) (k : ℕ) {a b : SL3}
    (ha : a ∈ liftedC (R.d k) (R.g k)) (hb : b ∈ liftedC (R.d k) (R.g k))
    (h : mkX a = mkX b) : a = b := by
  obtain ⟨v₁, hv₁, h1⟩ := ha
  obtain ⟨v₂, hv₂, h2⟩ := hb
  have hv4 : v₁ ∈ V (4 * R.d k) := V_mono' (by linarith [R.hdpos k]) hv₁
  have hv4' : v₂ ∈ V (4 * R.d k) := V_mono' (by linarith [R.hdpos k]) hv₂
  have e1 : v₁ * R.g k = a := h1
  have e2 : v₂ * R.g k = b := h2
  have hmk : v₁ • mkX (R.g k) = v₂ • mkX (R.g k) := by
    rw [← atomMSig_smul_mkX v₁ (R.g k), ← atomMSig_smul_mkX v₂ (R.g k), e1, e2, h]
  have hv : v₁ = v₂ := R.hinj k v₁ v₂ hv4 hv4' hmk
  rw [← e1, ← e2, hv]

/-! ## The `U`-saturation -/

/-- `satUC U O` is exactly the set of `g` some `U`-translate of which lies in `O`. -/
theorem mem_satUC_iff (U : Subgroup SL3) (O : Set SL3) (g : SL3) :
    g ∈ satUC U O ↔ ∃ u ∈ U, u * g ∈ O := by
  constructor
  · rintro ⟨u, huU, o, hoO, rfl⟩
    exact ⟨u⁻¹, U.inv_mem huU, by rw [inv_mul_cancel_left]; exact hoO⟩
  · rintro ⟨u, huU, hu⟩
    exact ⟨u⁻¹, U.inv_mem huU, u * g, hu, by rw [inv_mul_cancel_left]⟩

/-- Left `U`-multiplication does not change membership of `satUC U O`. -/
theorem satUC_mul_iff (U : Subgroup SL3) (O : Set SL3) {u g : SL3} (hu : u ∈ U) :
    u * g ∈ satUC U O ↔ g ∈ satUC U O := by
  rw [mem_satUC_iff, mem_satUC_iff]
  constructor
  · rintro ⟨u', hu'U, hu'⟩
    refine ⟨u' * u, U.mul_mem hu'U hu, ?_⟩
    rw [mul_assoc]
    exact hu'
  · rintro ⟨u', hu'U, hu'⟩
    refine ⟨u' * u⁻¹, U.mul_mem hu'U (U.inv_mem hu), ?_⟩
    rw [mul_assoc, inv_mul_cancel_left]
    exact hu'

/-- Membership of the saturation of a singleton. -/
theorem mem_satUC_singleton (U : Subgroup SL3) (z w : SL3) :
    w ∈ satUC U ({z} : Set SL3) ↔ ∃ u ∈ U, u * z = w := by
  constructor
  · rintro ⟨u, huU, o, ho, huo⟩
    rw [Set.mem_singleton_iff] at ho
    subst ho
    exact ⟨u, huU, huo⟩
  · rintro ⟨u, huU, rfl⟩
    exact ⟨u, huU, z, rfl, rfl⟩

/-! ## Membership in the clipped generators -/

/-- Inside a cell, membership in a clipped generator is membership of the lift in the saturation
of the generator set. -/
theorem mem_genCut_iff (R : RawCells U) {k m : ℕ} {z : X3} (hz : z ∈ R.Q k) :
    z ∈ genCut U R.Q R.d R.g R.O k m ↔ R.liftR k z ∈ satUC U (R.O m) := by
  constructor
  · intro h
    obtain ⟨⟨w, ⟨hwsat, hwl⟩, hwz⟩, -⟩ := h
    have hw : w = R.liftR k z :=
      mkX_inj_liftedR R k hwl (liftR_mem R k hz) (by rw [hwz, liftR_mkX R k hz])
    rwa [hw] at hwsat
  · intro h
    exact ⟨⟨R.liftR k z, ⟨h, liftR_mem R k hz⟩, liftR_mkX R k hz⟩, hz⟩

/-! ## The atom of the cut σ-algebra inside a cell -/

/-- **The atoms of the cut σ-algebra inside a cell.** -/
theorem atom_MSigCut (R : RawCells U) {k : ℕ} {y : X3} (hy : y ∈ R.Q k) :
    atom (MSigCut U R.Q R.d R.g R.O) y
      = mkX '' ({g : SL3 | ∃ u ∈ U, g = u * R.liftR k y} ∩ liftedC (R.d k) (R.g k))
        ∩ R.Q k := by
  classical
  have key : ∀ z : X3, z ∈ atom (MSigCut U R.Q R.d R.g R.O) y ↔
      ∀ s ∈ (Set.range R.Q ∪
        Set.range (fun p : ℕ × ℕ => genCut U R.Q R.d R.g R.O p.1 p.2)),
        (z ∈ s ↔ y ∈ s) := by
    intro z
    exact atomMSig_mem_atom_generateFrom
  ext z
  constructor
  · intro hz
    have hp := (key z).mp hz
    have hzQ : z ∈ R.Q k := (hp (R.Q k) (Or.inl ⟨k, rfl⟩)).mpr hy
    have hgen : ∀ m, z ∈ genCut U R.Q R.d R.g R.O k m ↔ y ∈ genCut U R.Q R.d R.g R.O k m :=
      fun m => hp (genCut U R.Q R.d R.g R.O k m) (Or.inr ⟨(k, m), rfl⟩)
    have hsat : ∀ m, R.liftR k z ∈ satUC U (R.O m) ↔ R.liftR k y ∈ satUC U (R.O m) :=
      fun m => ((mem_genCut_iff R hzQ).symm.trans (hgen m)).trans (mem_genCut_iff R hy)
    obtain ⟨u, huU, huz⟩ := (mem_satUC_singleton U (R.liftR k z) (R.liftR k y)).mp
      (R.hOsep (R.liftR k z) (R.liftR k y) hsat)
    have hwit : R.liftR k z = u⁻¹ * R.liftR k y := by
      rw [← huz]; rw [inv_mul_cancel_left]
    exact ⟨⟨R.liftR k z, ⟨⟨u⁻¹, U.inv_mem huU, hwit⟩, liftR_mem R k hzQ⟩,
      liftR_mkX R k hzQ⟩, hzQ⟩
  · rintro ⟨⟨w, ⟨hwW, hwl⟩, hwz⟩, hzQ⟩
    obtain ⟨u, huU, hwu⟩ := hwW
    have hℓw : R.liftR k z = w :=
      mkX_inj_liftedR R k (liftR_mem R k hzQ) hwl (by rw [liftR_mkX R k hzQ, hwz])
    have hℓ : R.liftR k z = u * R.liftR k y := by rw [hℓw, hwu]
    refine (key z).mpr fun s hs => ?_
    rcases hs with ⟨j, hj⟩ | ⟨⟨i, m⟩, him⟩
    · rw [← hj]
      by_cases hjk : j = k
      · rw [hjk]; exact ⟨fun _ => hy, fun _ => hzQ⟩
      · exact iff_of_false (Set.disjoint_left.mp (R.hdisj k j (Ne.symm hjk)) hzQ)
          (Set.disjoint_left.mp (R.hdisj k j (Ne.symm hjk)) hy)
    · rw [← him]
      by_cases hik : i = k
      · rw [hik, mem_genCut_iff R hzQ, mem_genCut_iff R hy, hℓ,
          satUC_mul_iff U (R.O m) huU]
      · exact iff_of_false
          (fun h => Set.disjoint_left.mp (R.hdisj i k hik) h.2 hzQ)
          (fun h => Set.disjoint_left.mp (R.hdisj i k hik) h.2 hy)

/-! ## The shape of an atom of the cut σ-algebra -/

/-- **The shape of an atom of `MSigCut`.** -/
theorem shape_MSigCut (R : RawCells U) {k : ℕ} {y : X3} (hy : y ∈ R.Q k)
    (hfree : ∀ u ∈ U, u • y = y → u = 1) :
    shape (MSigCut U R.Q R.d R.g R.O) U y
      = {u : SL3 | u ∈ U ∧ u * R.liftR k y ∈ liftedC (R.d k) (R.g k) ∧ u • y ∈ R.Q k} := by
  have hatom := atom_MSigCut R hy
  have hℓmk : mkX (R.liftR k y) = y := liftR_mkX R k hy
  ext u
  constructor
  · rintro ⟨huU, huA⟩
    rw [hatom] at huA
    obtain ⟨huA', huyQ⟩ := huA
    obtain ⟨g, hgmem, hgk⟩ := huA'
    obtain ⟨hgcos, hgl⟩ := hgmem
    obtain ⟨u₀, hu₀U, hgu⟩ := hgcos
    have hgl' : u₀ * R.liftR k y ∈ liftedC (R.d k) (R.g k) := by rw [← hgu]; exact hgl
    have huy : u • y = u₀ • y := by
      rw [← hgk, hgu, atomMSig_smul_mkX u₀ (R.liftR k y), hℓmk]
    have hfix : (u₀⁻¹ * u) • y = y := by rw [mul_smul, huy, inv_smul_smul]
    have hu_eq : u = u₀ := by
      have h1 : u₀⁻¹ * u = 1 := hfree _ (U.mul_mem (U.inv_mem hu₀U) huU) hfix
      calc u = u₀ * (u₀⁻¹ * u) := (mul_inv_cancel_left u₀ u).symm
        _ = u₀ * 1 := by rw [h1]
        _ = u₀ := mul_one u₀
    refine ⟨huU, ?_, huyQ⟩
    rw [hu_eq]
    exact hgl'
  · rintro ⟨huU, hgl, huyQ⟩
    refine ⟨huU, ?_⟩
    rw [hatom]
    refine ⟨⟨u * R.liftR k y, ⟨⟨u, huU, rfl⟩, hgl⟩, ?_⟩, huyQ⟩
    rw [atomMSig_smul_mkX u (R.liftR k y), hℓmk]

/-! ## The two geometric facts about the shape -/

/-- The shape is the trace of an open set on `U`. -/
theorem shape_trace_open {U : Subgroup SL3} {Q : Set X3} (hQ : IsOpen Q)
    {L : Set SL3} (hL : IsOpen L) (l : SL3) (y : X3) :
    ∃ W : Set SL3, IsOpen W ∧
      {u : SL3 | u ∈ U ∧ u * l ∈ L ∧ u • y ∈ Q} = W ∩ (U : Set SL3) := by
  refine ⟨(fun g : SL3 => g * l) ⁻¹' L ∩ (fun g : SL3 => g • y) ⁻¹' Q, ?_, ?_⟩
  · refine IsOpen.inter (hL.preimage ?_) (hQ.preimage ?_)
    · fun_prop
    · fun_prop
  · ext u
    constructor
    · rintro ⟨huU, h1, h2⟩
      exact ⟨⟨h1, h2⟩, huU⟩
    · rintro ⟨⟨h1, h2⟩, huU⟩
      exact ⟨huU, h1, h2⟩

/-- The entrywise `1 / 2` bound for `v * w⁻¹` with `v ∈ V δ`, `w ∈ V (δ / 2)`, `δ ≤ 1 / 16`. -/
theorem mem_Uball_half_of {U : Subgroup SL3} {δ : ℝ} (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16)
    {u v w : SL3} (huU : u ∈ U) (hu : u = v * w⁻¹) (hv : v ∈ V δ) (hw : w ∈ V (δ / 2)) :
    u ∈ Work.EKLComp.Uball U (1 / 2) := by
  have hδ2pos : 0 < δ / 2 := by linarith
  have hδ2le : δ / 2 ≤ 1 := by linarith
  have hwinv : w⁻¹ ∈ V (10 * (δ / 2)) := Work.EKLComp.inv_mem_V hδ2pos hδ2le hw
  have hV : v * w⁻¹ ∈ V (δ + 10 * (δ / 2) + 3 * δ * (10 * (δ / 2))) :=
    V_mul_subset_V (le_of_lt hδ) (by positivity) hv hwinv
  have hd2 : δ * δ ≤ δ / 16 := by
    have h := mul_le_mul_of_nonneg_left hδ16 (le_of_lt hδ)
    linarith [h]
  have hbound : δ + 10 * (δ / 2) + 3 * δ * (10 * (δ / 2)) ≤ 1 / 2 := by
    nlinarith [hδ, hδ16, hd2]
  have hV' : v * w⁻¹ ∈ V (1 / 2) := V_mono' hbound hV
  refine ⟨huU, fun i j => ?_⟩
  rw [hu]
  exact hV' i j

end Work.EKLC6Core

namespace Work.EKLC6Core

theorem cellsData_atom_facts {U : Subgroup Work.EKLContract.SL3}
    {Q : ℕ → Set Work.EKLContract.X3} {d : ℕ → ℝ} {g : ℕ → Work.EKLContract.SL3}
    {O : ℕ → Set Work.EKLContract.SL3}
    (hopen : ∀ k, IsOpen (Q k))
    (hdisj : ∀ k l, k ≠ l → Disjoint (Q k) (Q l))
    (hdpos : ∀ k, 0 < d k) (hdsmall : ∀ k, d k ≤ 1 / 16)
    (hsub : ∀ k, Q k ⊆ (fun v : Work.EKLContract.SL3 => v • Work.EKLContract.mkX (g k)) ''
      (Work.EKLContract.V (d k / 2)))
    (hinj : ∀ k (v₁ v₂ : Work.EKLContract.SL3), v₁ ∈ Work.EKLContract.V (4 * d k) →
      v₂ ∈ Work.EKLContract.V (4 * d k) →
      v₁ • Work.EKLContract.mkX (g k) = v₂ • Work.EKLContract.mkX (g k) → v₁ = v₂)
    (hOopen : ∀ m, IsOpen (O m))
    (hOvis : ∀ z : Work.EKLContract.SL3, ∃ m, z ∈ Work.EKLC6Core.satUC U (O m))
    (hOsep : ∀ z w : Work.EKLContract.SL3,
      (∀ m, (z ∈ Work.EKLC6Core.satUC U (O m) ↔ w ∈ Work.EKLC6Core.satUC U (O m))) →
      w ∈ Work.EKLC6Core.satUC U ({z} : Set Work.EKLContract.SL3))
    {k : ℕ} {y : Work.EKLContract.X3} (hy : y ∈ Q k)
    (hfree : ∀ u ∈ U, u • y = y → u = 1) :
    Work.EKLContract.atom (Work.EKLC6Core.MSigCut U Q d g O) y ⊆ Q k ∧
    Work.EKLContract.atom (Work.EKLC6Core.MSigCut U Q d g O) y ⊆
      (fun u : Work.EKLContract.SL3 => u • y) '' (U : Set Work.EKLContract.SL3) ∧
    (∃ W : Set Work.EKLContract.SL3, IsOpen W ∧
      Work.EKLContract.shape (Work.EKLC6Core.MSigCut U Q d g O) U y =
        W ∩ (U : Set Work.EKLContract.SL3)) ∧
    Work.EKLContract.shape (Work.EKLC6Core.MSigCut U Q d g O) U y ⊆
      Work.EKLComp.Uball U (1 / 2) := by
  classical
  let R : RawCells U :=
    { Q := Q, d := d, g := g, O := O, hopen := hopen, hdisj := hdisj, hdpos := hdpos,
      hdsmall := hdsmall, hsub := hsub, hinj := hinj, hOopen := hOopen, hOsep := hOsep }
  change atom (MSigCut U R.Q R.d R.g R.O) y ⊆ R.Q k ∧
    atom (MSigCut U R.Q R.d R.g R.O) y ⊆ (fun u : SL3 => u • y) '' (U : Set SL3) ∧
    (∃ W : Set SL3, IsOpen W ∧
      shape (MSigCut U R.Q R.d R.g R.O) U y = W ∩ (U : Set SL3)) ∧
    shape (MSigCut U R.Q R.d R.g R.O) U y ⊆ Work.EKLComp.Uball U (1 / 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    have hp := (atomMSig_mem_atom_generateFrom (b := Set.range R.Q ∪
      Set.range (fun p : ℕ × ℕ => genCut U R.Q R.d R.g R.O p.1 p.2)) (x := y) (z := z)).mp hz
    exact (hp (R.Q k) (Or.inl ⟨k, rfl⟩)).mpr hy
  · intro z hz
    rw [atom_MSigCut R hy] at hz
    obtain ⟨⟨w, ⟨hwW, hwl⟩, hwz⟩, -⟩ := hz
    obtain ⟨u, huU, hwu⟩ := hwW
    have hgoal : u • y = z := by
      rw [← liftR_mkX R k hy, ← atomMSig_smul_mkX u (R.liftR k y), ← hwu]
      exact hwz
    exact ⟨u, huU, hgoal⟩
  · obtain ⟨W, hW, hWeq⟩ := shape_trace_open (U := U) (Q := R.Q k) (hopen k)
      (isOpen_liftedC (R.d k) (R.g k)) (R.liftR k y) y
    refine ⟨W, hW, ?_⟩
    rw [shape_MSigCut R hy hfree, hWeq]
  · intro u hu
    rw [shape_MSigCut R hy hfree] at hu
    obtain ⟨huU, hgl, -⟩ := hu
    obtain ⟨v, hv, hv_eq⟩ := hgl
    obtain ⟨w, hw, hw_eq⟩ := liftR_mem_half R k hy
    have hv_eq' : v * R.g k = u * R.liftR k y := by simpa using hv_eq
    have hw_eq' : w * R.g k = R.liftR k y := by simpa using hw_eq
    have h1 : v * R.g k = (u * w) * R.g k := by rw [mul_assoc, hw_eq', ← hv_eq']
    have huv : v = u * w := mul_right_cancel h1
    have hueq : u = v * w⁻¹ := by rw [huv, mul_inv_cancel_right]
    exact mem_Uball_half_of (U := U) (R.hdpos k) (R.hdsmall k) huU hueq hv hw

end Work.EKLC6Core
