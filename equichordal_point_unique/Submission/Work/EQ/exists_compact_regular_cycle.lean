import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.ShiftCore
import Submission.Work.EQ.ChainReading
import Submission.Work.EQ.compact_mod_punctures_of_tails
import Submission.Work.EQ.CDFree

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN.md, DESIGN_CORE.md and PAPER_PROOFS.md (the lead's full paper proofs for the sketched Rychlik steps; follow them). Defs: Submission/Work/EQ/Defs.lean + DefsCore.lean (namespace Work.EQ; do NOT edit; IsPuncturedChart now carries a scale κ). Proved UNIFORMIZATION library in this workspace (Submission.UnifMain etc.). With UnifMain imported write `open _root_.Topology`.

# exists_compact_regular_cycle: minimal regular cycle compact mod σ (Rychlik Thm 8(1)–(3)) (6–10k; READY as stated)

**Proof.** `PAPER_PROOFS.md` §5. Lemma 5.1 (limits over an annulus `A`) has three cases:
* (a) `fan_trichotomy` case (iii) is impossible (`no_near_axis_segment`). **Rychlik omits this case.**
* (b) A case-(ii) side gives, through a co-countable pointwise limit plus F3 branch counting and
  `exists_regular_of_family`, a regular component with value `c₀μ₁μ₂`, where `|μ₁μ₂| ≤ μ_max < 1`.
* (c) Both sides constant give finitely many values and components (`fan η₀` is injective near 0).

Then:
* the minimum `ρ*` is attained;
* there are finitely many minimal components;
* `σ` permutes them, so some `σᵈ` fixes one;
* the word set over `A` is finite, and F3 gives the compact part plus finitely many κ-punctured
  charts.

Uses: `fan_trichotomy` (corrected), `fan_estimates`, `charVal_props`, `no_near_axis_segment`,
`exists_regular_of_family`, `H0_invParam_ge`, `H0_structure`.
-/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-! ## Reading a chain over an annulus

A chain `p ∈ ⁰H` whose forward tail is the stable germ from index `N` on and whose backward tail
is the unstable germ from index `-N` on has a *stable word* `ε` of length `N` and an *unstable
word* `η` with `p 0 = fan ε (ψ₁ p)` and `p(-N) = mirror (fan η (λ^N ψ₂ p))`.  These words are the
labels used in the compactness argument of Rychlik Thm 8. -/

/-! ## Rychlik's fact F1: regular pairs are exactly the pairs avoiding `O₁`, `O₂`

`RegPair a P Q` is `EqRelC a P Q` together with the nonvanishing of the two radicands
`ρ(P)² = (P.1 - a/2)² + P.2²` and `ρ'(Q)² = (Q.1 + a/2)² + Q.2²`.  Since `P + Q` is a *unit*
vector of the bilinear form parallel to both `P - O₂` and `Q - O₁`, the radicands can only vanish
at `P = O₂` resp. `Q = O₁`. -/

/-! The points `O₂ = (a/2, 0)` and `O₁ = (-a/2, 0)` are those of `Submission.Work.EQ.bp_aux`
(imported below through the compactness lemma); we reuse them rather than redeclaring. -/

theorem subO2_eq_zero_iff {a : ℝ} {P : ℂ × ℂ} : subO2 a P = 0 ↔ P = O2 a := by
  constructor
  · intro h
    have h1 : P.1 - ((a / 2 : ℝ) : ℂ) = 0 := by
      simpa [subO2, Prod.fst_zero] using congrArg Prod.fst h
    have h2 : P.2 = 0 := by simpa [subO2, Prod.snd_zero] using congrArg Prod.snd h
    ext
    · show P.1 = ((a / 2 : ℝ) : ℂ)
      linear_combination h1
    · exact h2
  · intro h; rw [h]; ext <;> simp [subO2, O2]

theorem subO1_eq_zero_iff {a : ℝ} {Q : ℂ × ℂ} : subO1 a Q = 0 ↔ Q = O1 a := by
  constructor
  · intro h
    have h1 : Q.1 + ((a / 2 : ℝ) : ℂ) = 0 := by
      simpa [subO1, Prod.fst_zero] using congrArg Prod.fst h
    have h2 : Q.2 = 0 := by simpa [subO1, Prod.snd_zero] using congrArg Prod.snd h
    ext
    · show Q.1 = -(((a / 2 : ℝ)) : ℂ)
      linear_combination h1
    · exact h2
  · intro h; rw [h]; ext <;> simp [subO1, O1]


open Complex Filter _root_.Topology


open Classical

/-! ## Elementary consequences of the structure of `⁰H` -/

/-- `ρ*` is positive as soon as `⁰H` has a regular component: this is Rychlik's Lemma 17
(`H0_invParam_ge`, proved in the workspace). -/
theorem rhoStar_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hne : (RegValues a h).Nonempty) : 0 < rhoStar a h := by
  obtain ⟨ρ, hρ0, hρ⟩ := H0_invParam_ge ha0 ha1 hh
  have hmem : ∀ x ∈ {x : ℝ | ∃ c, c ∈ RegValues a h ∧ x = ‖c‖}, ρ ≤ x := by
    rintro x ⟨c, hc, rfl⟩
    obtain ⟨p, hp, hval⟩ := hc
    rw [← hval p (mem_connectedComponentIn hp)]
    exact hρ p hp
  have hne' : {x : ℝ | ∃ c, c ∈ RegValues a h ∧ x = ‖c‖}.Nonempty := by
    obtain ⟨c, hc⟩ := hne
    exact ⟨‖c‖, c, hc, rfl⟩
  exact lt_of_lt_of_le hρ0 (le_csInf hne' hmem)

/-- `ψ = ψ₁ψ₂` is invariant under the shift. -/
theorem hShift_mul {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (q : ChainData) :
    (hShift a q).2.1 * (hShift a q).2.2 = q.2.1 * q.2.2 := by
  have hlam : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ShiftCore.eqLam_ne_zero_of ha0 ha1)
  simp only [hShift]
  field_simp

/-- The shift maps connected components of `⁰H` onto connected components of `⁰H`. -/
theorem hShift_image_connectedComponentIn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r) {p : ChainData} (hp : p ∈ H0 a h) :
    hShift a '' connectedComponentIn (H0 a h) p
      = connectedComponentIn (H0 a h) (hShift a p) := by
  have hp' : hShift a p ∈ H0 a h := ShiftCore.hShift_mem_H0 ha0 ha1 hp
  have hsub : hShift a '' connectedComponentIn (H0 a h) p
      ⊆ connectedComponentIn (H0 a h) (hShift a p) := by
    have hconn : IsPreconnected (hShift a '' connectedComponentIn (H0 a h) p) :=
      IsPreconnected.image (s := connectedComponentIn (H0 a h) p)
        isPreconnected_connectedComponentIn (hShift a) (ShiftCore.continuous_hShift a).continuousOn
    have hsubF : hShift a '' connectedComponentIn (H0 a h) p ⊆ H0 a h := by
      rintro q ⟨q₀, hq₀, rfl⟩
      exact ShiftCore.hShift_mem_H0 ha0 ha1 (connectedComponentIn_subset (H0 a h) p hq₀)
    exact hconn.subset_connectedComponentIn ⟨p, mem_connectedComponentIn hp, rfl⟩ hsubF
  refine Set.Subset.antisymm hsub ?_
  intro q hq
  have hpre_conn : IsPreconnected
      (ShiftCore.hShiftInv a '' connectedComponentIn (H0 a h) (hShift a p)) :=
    IsPreconnected.image (s := connectedComponentIn (H0 a h) (hShift a p))
      isPreconnected_connectedComponentIn (ShiftCore.hShiftInv a) (ShiftCore.continuous_hShiftInv a).continuousOn
  have hsubF : ShiftCore.hShiftInv a '' connectedComponentIn (H0 a h) (hShift a p) ⊆ H0 a h := by
    rintro q' ⟨q₀, hq₀, rfl⟩
    exact ShiftCore.hShiftInv_mem_H0 ha0 ha1 (connectedComponentIn_subset (H0 a h) (hShift a p) hq₀)
  have hp_mem : p ∈ ShiftCore.hShiftInv a '' connectedComponentIn (H0 a h) (hShift a p) :=
    ⟨hShift a p, mem_connectedComponentIn hp', ShiftCore.hShift_inv_eq ha0 ha1 p⟩
  have hmem : ShiftCore.hShiftInv a q ∈ connectedComponentIn (H0 a h) p :=
    hpre_conn.subset_connectedComponentIn hp_mem hsubF ⟨q, hq, rfl⟩
  exact ⟨ShiftCore.hShiftInv a q, hmem, ShiftCore.hShift_inv_eq' ha0 ha1 q⟩




open Complex Filter _root_.Topology

/-- `CompactModPunctures` is monotone in the set. -/
theorem CompactModPunctures_mono {a : ℝ} {h : ℂ → ℂ} {S T : Set ChainData} (hST : S ⊆ T) :
    CompactModPunctures a h T → CompactModPunctures a h S := by
  intro hT K hK h0
  obtain ⟨C, hC, hCsub, m, e, u₀, k, hcharts, hcover⟩ := hT K hK h0
  exact ⟨C, hC, hCsub, m, e, u₀, k, hcharts, fun q hq => hcover ⟨hST hq.1, hq.2⟩⟩


open Complex Filter _root_.Topology

/-! ## The cyclic permutation of the minimal components -/

/-- Iterates of the shift keep `⁰H`. -/
theorem hShift_iterate_mem_H0 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {q : ChainData}
    (hq : q ∈ H0 a h) (j : ℕ) : (hShift a)^[j] q ∈ H0 a h := by
  induction j with
  | zero => simpa using hq
  | succ j ih => rw [Function.iterate_succ_apply']; exact ShiftCore.hShift_mem_H0 ha0 ha1 ih

/-- The invariant parameter is preserved by iterates of the shift. -/
theorem hShift_iterate_mul {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (q : ChainData) (j : ℕ) :
    ((hShift a)^[j] q).2.1 * ((hShift a)^[j] q).2.2 = q.2.1 * q.2.2 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (hShift_mul ha0 ha1 ((hShift a)^[j] q)).trans ih



/-- **The shift permutes the minimal components.** -/
theorem hShift_image_mem_range {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {m : ℕ} {S : Fin m → Set ChainData} {c : Fin m → ℂ}
    (hreg : ∀ i, IsRegComp a h (S i) (c i) ∧ ‖c i‖ = rhoStar a h)
    (hexh : ∀ S' : Set ChainData, ∀ c' : ℂ, IsRegComp a h S' c' → ‖c'‖ = rhoStar a h →
      ∃ i, S' = S i) :
    ∀ S' ∈ Set.range S, hShift a '' S' ∈ Set.range S := by
  rintro S' ⟨i, rfl⟩
  obtain ⟨hsub, ⟨p, hp, hcomp⟩, hval⟩ := (hreg i).1
  have hp' : hShift a p ∈ H0 a h := ShiftCore.hShift_mem_H0 ha0 ha1 hp
  have hcomp' : hShift a '' S i = connectedComponentIn (H0 a h) (hShift a p) := by
    rw [hcomp]
    exact hShift_image_connectedComponentIn ha0 ha1 hh hp
  have hreg' : IsRegComp a h (hShift a '' S i) (c i) := by
    refine ⟨?_, ⟨hShift a p, hp', hcomp'⟩, ?_⟩
    · rintro q ⟨q₀, hq₀, rfl⟩
      exact ShiftCore.hShift_mem_H0 ha0 ha1 (hsub hq₀)
    · rintro q ⟨q₀, hq₀, rfl⟩
      rw [hShift_mul ha0 ha1]
      exact hval q₀ hq₀
  obtain ⟨j, hj⟩ := hexh _ _ hreg' (hreg i).2
  exact Set.mem_range.mpr ⟨j, hj.symm⟩

/-- An iterate of the image map is the image of the iterate. -/
theorem iterate_image_eq {α : Type*} (f : α → α) (Y : Set α) (k : ℕ) :
    (fun X : Set α => f '' X)^[k] Y = f^[k] '' Y := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ']
      exact (Set.image_comp f (f^[k]) Y).symm

/-- One step of the iterate of the image map. -/
theorem iterate_image_succ_eq {α : Type*} (f : α → α) (Y : Set α) (k : ℕ) :
    f^[k + 1] '' Y = f '' (f^[k] '' Y) := by
  rw [Function.iterate_succ', Set.image_comp]

/-- **Some power of the shift fixes a prescribed minimal component.** -/
theorem exists_shift_iterate_fixing {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {m : ℕ} (hm : 0 < m) {S : Fin m → Set ChainData} {c : Fin m → ℂ}
    (hreg : ∀ i, IsRegComp a h (S i) (c i) ∧ ‖c i‖ = rhoStar a h)
    (hexh : ∀ S' : Set ChainData, ∀ c' : ℂ, IsRegComp a h S' c' → ‖c'‖ = rhoStar a h →
      ∃ i, S' = S i)
    (i₀ : Fin m) :
    ∃ d : ℕ, 0 < d ∧ (hShift a)^[d] '' S i₀ = S i₀ := by
  have hTshift : ∀ S' ∈ Set.range S, hShift a '' S' ∈ Set.range S :=
    hShift_image_mem_range ha0 ha1 hh hreg hexh
  have hinj : Function.Injective (hShift a) := by
    intro p q hpq
    have h1 : ShiftCore.hShiftInv a (hShift a p) = ShiftCore.hShiftInv a (hShift a q) := congrArg (ShiftCore.hShiftInv a) hpq
    rwa [ShiftCore.hShift_inv_eq ha0 ha1 p, ShiftCore.hShift_inv_eq ha0 ha1 q] at h1
  have hsetinj : Function.Injective (fun X : Set ChainData => hShift a '' X) := by
    intro X Y hXY
    have hXY' : hShift a '' X = hShift a '' Y := hXY
    ext q
    constructor
    · intro hq
      have hmem : hShift a q ∈ hShift a '' Y := by rw [← hXY']; exact ⟨q, hq, rfl⟩
      obtain ⟨q', hq', hq''⟩ := hmem
      rwa [hinj hq''] at hq'
    · intro hq
      have hmem : hShift a q ∈ hShift a '' X := by rw [hXY']; exact ⟨q, hq, rfl⟩
      obtain ⟨q', hq', hq''⟩ := hmem
      rwa [hinj hq''] at hq'
  have horbfin : (Set.range fun k : ℕ => (hShift a)^[k] '' S i₀).Finite := by
    refine (Set.finite_range S).subset ?_
    rintro X ⟨k, rfl⟩
    induction k with
    | zero => exact ⟨i₀, by simp⟩
    | succ k ih =>
        show (hShift a)^[k + 1] '' S i₀ ∈ Set.range S
        rw [iterate_image_succ_eq]
        exact hTshift _ ih
  obtain ⟨j₁, j₂, hj₁₂, heq⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem
      (t := Set.range fun k : ℕ => (hShift a)^[k] '' S i₀)
      (f := fun k : ℕ => (hShift a)^[k] '' S i₀) (fun k => ⟨k, rfl⟩) horbfin
  have hd : 0 < j₂ - j₁ := Nat.sub_pos_of_lt hj₁₂
  refine ⟨j₂ - j₁, hd, ?_⟩
  have h2 : (hShift a)^[j₂] '' S i₀ = (hShift a)^[j₁] '' ((hShift a)^[j₂ - j₁] '' S i₀) := by
    nth_rewrite 1 [show j₂ = j₁ + (j₂ - j₁) from (Nat.add_sub_cancel' hj₁₂.le).symm]
    rw [Function.iterate_add]
    exact Set.image_comp ((hShift a)^[j₁]) ((hShift a)^[j₂ - j₁]) (S i₀)
  have hinj2 : Function.Injective (fun X : Set ChainData => (hShift a)^[j₁] '' X) := by
    rw [show (fun X : Set ChainData => (hShift a)^[j₁] '' X)
        = (fun X : Set ChainData => hShift a '' X)^[j₁] from
      funext fun X => (iterate_image_eq (hShift a) X j₁).symm]
    exact hsetinj.iterate j₁
  rw [h2] at heq
  exact (hinj2 heq).symm



open Complex Filter _root_.Topology

/-- **A minimal regular cycle is compact modulo `σ` (Rychlik Thm 8(1)–(3)).** If some
component of `H0` is regular, then some regular component is carried into itself by a power
`σᵈ` of the shift and is compact modulo finitely many punctures over compact sets of `ℂ*`. -/
theorem exists_compact_regular_cycle {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r)
    (hreg : ∃ p ∈ H0 a h, ∃ c : ℂ, ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c) :
    ∃ p ∈ H0 a h, ∃ c : ℂ, (∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c) ∧
      ∃ d : ℕ, 0 < d ∧
        (∀ q ∈ connectedComponentIn (H0 a h) p,
          (hShift a)^[d] q ∈ connectedComponentIn (H0 a h) p) ∧
        CompactModPunctures a h (connectedComponentIn (H0 a h) p) := by
  obtain ⟨p₀, hp₀, c₀, hc₀⟩ := hreg
  have hregComp : IsRegComp a h (connectedComponentIn (H0 a h) p₀) c₀ :=
    ⟨fun q hq => connectedComponentIn_subset (H0 a h) p₀ hq, ⟨p₀, hp₀, rfl⟩, hc₀⟩
  have hpos : 0 < rhoStar a h := rhoStar_pos ha0 ha1 hh ⟨c₀, p₀, hp₀, hc₀⟩
  obtain ⟨r₁, r₂, N, m, S, c, hm, hr₁, hr₁₂, hratio, hN₁, hN₂, hSreg, hexh, htail⟩ :=
    CDFree.minimal_cycle_data ha0 ha1 hh hpos ⟨connectedComponentIn (H0 a h) p₀, c₀, hregComp⟩
  obtain ⟨i₀⟩ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨d, hd, hfix⟩ := exists_shift_iterate_fixing ha0 ha1 hh hm hSreg hexh i₀
  set U : Set ChainData := ⋃ j : ℕ, (fun q => (hShift a)^[j] q) '' S i₀ with hUdef
  have hTshift : ∀ S' ∈ Set.range S, hShift a '' S' ∈ Set.range S :=
    hShift_image_mem_range ha0 ha1 hh hSreg hexh
  have hiter_mem : ∀ j : ℕ, (hShift a)^[j] '' S i₀ ∈ Set.range S := by
    intro j
    induction j with
    | zero => exact ⟨i₀, by simp⟩
    | succ j ih =>
        show (hShift a)^[j + 1] '' S i₀ ∈ Set.range S
        rw [iterate_image_succ_eq]
        exact hTshift _ ih
  have hUmem : ∀ q : ChainData, q ∈ U ↔ ∃ (j : ℕ) (q' : ChainData),
      q' ∈ S i₀ ∧ (hShift a)^[j] q' = q := by
    intro q
    rw [hUdef]
    constructor
    · intro hq
      obtain ⟨j, q', hq', hq''⟩ := Set.mem_iUnion.mp hq
      exact ⟨j, q', hq', hq''⟩
    · rintro ⟨j, q', hq', hq''⟩
      exact Set.mem_iUnion.mpr ⟨j, q', hq', hq''⟩
  have hUsub : U ⊆ H0 a h := by
    intro q hq
    obtain ⟨j, q', hq', rfl⟩ := (hUmem q).mp hq
    exact hShift_iterate_mem_H0 ha0 ha1 ((hSreg i₀).1.1 hq') j
  have hUval : ∀ q ∈ U, q.2.1 * q.2.2 = c i₀ := by
    intro q hq
    obtain ⟨j, q', hq', rfl⟩ := (hUmem q).mp hq
    rw [hShift_iterate_mul ha0 ha1 q' j]
    exact (hSreg i₀).1.2.2 q' hq'
  have hUclosed : ∀ q ∈ U, ∀ q' ∈ connectedComponentIn (H0 a h) q, q' ∈ U := by
    intro q hq q' hq'
    obtain ⟨j, q'', hq'', rfl⟩ := (hUmem q).mp hq
    obtain ⟨i, hi⟩ := hiter_mem j
    have hmem : (hShift a)^[j] q'' ∈ S i := by rw [hi]; exact ⟨q'', hq'', rfl⟩
    obtain ⟨-, ⟨pᵢ, hpᵢ, hcomp⟩, -⟩ := (hSreg i).1
    have hmemS : q' ∈ S i := by
      have h1 : connectedComponentIn (H0 a h) ((hShift a)^[j] q'')
          = connectedComponentIn (H0 a h) pᵢ :=
        (connectedComponentIn_eq (hcomp ▸ hmem)).symm
      rw [h1, ← hcomp] at hq'
      exact hq'
    rw [hi] at hmemS
    obtain ⟨qv, hqv, hqveq⟩ := hmemS
    exact (hUmem q').mpr ⟨j, qv, hqv, hqveq⟩
  have hUcyc : hShift a '' U = U := by
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩
      obtain ⟨j, q'', hq'', hqj⟩ := (hUmem q').mp hq'
      refine (hUmem (hShift a q')).mpr ⟨j + 1, q'', hq'', ?_⟩
      rw [← hqj]
      exact Function.iterate_succ_apply' (hShift a) j q''
    · intro hq
      obtain ⟨j, q'', hq'', hqj⟩ := (hUmem q).mp hq
      rcases j with _ | j
      · have hq''eq : q = q'' := by simpa using hqj.symm
        have hmem : q'' ∈ (hShift a)^[d] '' S i₀ := by rw [hfix]; exact hq''
        obtain ⟨y, hy, hy'⟩ := hmem
        refine ⟨(hShift a)^[d - 1] y, (hUmem _).mpr ⟨d - 1, y, hy, rfl⟩, ?_⟩
        have hstep : hShift a ((hShift a)^[d - 1] y) = q'' := by
          have h2 : (hShift a)^[(d - 1).succ] y = (hShift a)^[d] y := by
            rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ d)]
          exact ((Function.iterate_succ_apply' (hShift a) (d - 1) y).symm.trans h2).trans hy'
        rw [hstep, ← hq''eq]
      · refine ⟨(hShift a)^[j] q'', (hUmem _).mpr ⟨j, q'', hq'', rfl⟩, ?_⟩
        rw [← hqj]
        exact (Function.iterate_succ_apply' (hShift a) j q'').symm
  have hUcyc' : ∀ q : ChainData, q ∈ U ↔ hShift a q ∈ U := by
    intro q
    constructor
    · intro hq; rw [← hUcyc]; exact ⟨q, hq, rfl⟩
    · intro hq
      rw [← hUcyc] at hq
      obtain ⟨q', hq', heq⟩ := hq
      have hinj : Function.Injective (hShift a) := by
        intro p rr hpr
        have h1 : ShiftCore.hShiftInv a (hShift a p) = ShiftCore.hShiftInv a (hShift a rr) :=
          congrArg (ShiftCore.hShiftInv a) hpr
        rwa [ShiftCore.hShift_inv_eq ha0 ha1 p, ShiftCore.hShift_inv_eq ha0 ha1 rr] at h1
      rwa [hinj heq] at hq'
  have htailU : ∃ (r₁ r₂ : ℝ) (N : ℕ), 0 < r₁ ∧ r₁ < r₂ ∧ r₂ / r₁ > 1 / eqLam a ∧
      (eqLam a : ℝ) ^ N * r₂ < r ∧ (eqLam a : ℝ) ^ N * ‖c i₀‖ / r₁ < r ∧
      ∀ q ∈ U, q.2.1 ∈ Ann r₁ r₂ →
        (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1)) ∧
        (∀ n : ℕ, N ≤ n → q.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.2)) := by
    refine ⟨r₁, r₂, N, hr₁, hr₁₂, hratio, hN₁, ?_, ?_⟩
    · rw [(hSreg i₀).2]; exact hN₂
    · intro q hq hqA
      obtain ⟨j, q', hq', rfl⟩ := (hUmem q).mp hq
      obtain ⟨i, hi⟩ := hiter_mem j
      have hmem : (hShift a)^[j] q' ∈ S i := by rw [hi]; exact ⟨q', hq', rfl⟩
      exact htail i _ hmem hqA
  have hcne : c i₀ ≠ 0 := by
    intro h0
    have h1 : ‖c i₀‖ = rhoStar a h := (hSreg i₀).2
    rw [h0] at h1
    simp at h1
    linarith [hpos, h1]
  have hcptU : CompactModPunctures a h U :=
    compact_mod_punctures_of_tails ha0 ha1 hh hUsub hcne hUval hUclosed hUcyc' htailU
  obtain ⟨-, ⟨p₁, hp₁, hcomp₁⟩, hval₁⟩ := (hSreg i₀).1
  refine ⟨p₁, hp₁, c i₀, ?_, d, hd, ?_, ?_⟩
  · rw [← hcomp₁]
    exact hval₁
  · intro q hq
    rw [← hcomp₁] at hq ⊢
    rw [← hfix]
    exact ⟨q, hq, rfl⟩
  · rw [← hcomp₁]
    exact CompactModPunctures_mono (a := a) (h := h) (S := S i₀) (T := U)
      (fun q hq => (hUmem q).mpr ⟨0, q, hq, rfl⟩) hcptU

end

end Work.EQ
