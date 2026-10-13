/-
  WilC4/DeepThetaGDefs : the index bookkeeping behind `Work.WilC4.deepThetaG_definable`.

  `Work.WilC4.DeepThetaG Y B₀ ⊆ ℝ²` is the graph of the greatest lower bound `Θ(β)` of the
  numbers contributed by the bad points at scale `β` (see `Work.WilC4.DeepRatioDefs`).  Its
  `∅`-definability is a quantifier-bookkeeping exercise, organised here as follows.

  * `DRatBody Y` is the *quantifier-free body* of `DeepRatSet`, with **every** quantified
    variable free: the free block is `Fin 2` (`(β, t)`, the graph coordinates) and the quantified
    block is `Fin k ⊕ Fin 11` (`c` and `(x, w, y, y₂, v, y₀, A, B, z, z₂, q₀)`, where `z = 2x`,
    `z₂ = βx` and `q₀ = x/β` are the auxiliary slots needed to turn the substitutions
    `Gr Y c (2x) y₂`, `Gr Y c (βx) v`, `Gr Y c (x/β) y₀` into plain reindexings `GrSub`).
  * `DeepBodyNeg B₀` is the body of the *negation* of the deepness condition `IsDeepR B₀ c β x`
    (with `b` and `q₁ = x/(2β)` free), and `DRDeep B₀` is its universal projection.
  * `DRg Y B₀ = {(β,t) | t ∈ DeepRatSet Y B₀ β}` is the projection of `DRatBody ∩ DRDeep`,
    i.e. the graph of the set-valued `DeepRatSet` (proved in `mem_DRg_iff`).
  * `DRLower` is the graph of the "is a lower bound of `DeepRatSet Y B₀ β`" relation and `DRLUB`
    the graph of the "is above every lower bound" relation; `DeepThetaG_eq` assembles them into
    `DeepThetaG`.
-/
import Mathlib
import Submission.Work.WilC4.DeepRatioDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)
open Work.WilC4.Route (Gr)

variable {k : ℕ}

/-! ## 1. The index type -/

/-- The index block of the body of `DeepRatSet`: `Fin 2` carries the graph coordinates `(β, t)`,
`Fin k` carries the parameter `c`, and `Fin 11` carries the reals
`(x, w, y, y₂, v, y₀, A, B, z, z₂, q₀)` — the nine existentially quantified reals plus the three
auxiliary slots `z = 2x`, `z₂ = βx`, `q₀ = x/β`. -/
abbrev DRIdx (k : ℕ) := Fin 2 ⊕ (Fin k ⊕ Fin 11)

/-- The slot of `β = v 0`. -/
abbrev dβ {k : ℕ} : DRIdx k := Sum.inl (0 : Fin 2)
/-- The slot of the value `t = v 1`. -/
abbrev dt {k : ℕ} : DRIdx k := Sum.inl (1 : Fin 2)
/-- The slot of the parameter `c i`. -/
abbrev dc {k : ℕ} (i : Fin k) : DRIdx k := Sum.inr (Sum.inl i)
/-- The slot of the base point `x`. -/
abbrev dx {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (0 : Fin 11))
/-- The slot of the doubling ratio `w`. -/
abbrev dw {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (1 : Fin 11))
/-- The slot of the fibre value `y` at `x`. -/
abbrev dy {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (2 : Fin 11))
/-- The slot of the fibre value `y₂` at `2x`. -/
abbrev dy2 {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (3 : Fin 11))
/-- The slot of the fibre value `v` at `βx`. -/
abbrev dv {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (4 : Fin 11))
/-- The slot of the fibre value `y₀` at `x/β`. -/
abbrev dy0 {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (5 : Fin 11))
/-- The slot of the quotient `A = v / y`. -/
abbrev dA {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (6 : Fin 11))
/-- The slot of the quotient `B = y / y₀`. -/
abbrev dB {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (7 : Fin 11))
/-- The auxiliary slot of `z = 2x`. -/
abbrev dz {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (8 : Fin 11))
/-- The auxiliary slot of `z₂ = βx`. -/
abbrev dz2 {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (9 : Fin 11))
/-- The auxiliary slot of `q₀ = x/β`. -/
abbrev dq0 {k : ℕ} : DRIdx k := Sum.inr (Sum.inr (10 : Fin 11))

/-- The parameter map for `GrSub`: its head is the (unused) scale slot `dβ`, its tail reads off
`dc`, so that `GrSub Y embD a b` says "the value at `a` is `b` for the fibre of `Y` at `dc`". -/
abbrev embD {k : ℕ} : Fin (k + 1) → DRIdx k := Fin.cons dβ dc

/-- `GrSub Y embD a b` in terms of `Gr`. -/
theorem grSub_embD {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (a b : DRIdx k) :
    GrSub Y embD a b = {g : DRIdx k → ℝ | Gr Y (fun i => g (dc i)) (g a) (g b)} := by
  ext g
  simp only [GrSub, Set.mem_ofPred_eq, Gr]
  have h : (g ∘ (embD ∘ Fin.succ)) = (fun i => g (dc i)) := by
    funext i
    simp [embD]
  rw [h]

/-! ## 2. The body of `DeepRatSet` -/

/-- The quantifier-free body of `DeepRatSet`, with all the quantified variables free. -/
def DRatBody {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) : Set (DRIdx k → ℝ) :=
  {g | 0 < g dx ∧
       g ∈ GrSub Y embD dx dy ∧
       g dy ≠ 0 ∧
       g ∈ GrSub Y embD dz dy2 ∧
       g dz = 2 * g dx ∧
       g dw * g dy = g dy2 ∧
       (g dβ ≤ g dw ∨ g dw ≤ -g dβ) ∧
       g ∈ GrSub Y embD dz2 dv ∧
       g dz2 = g dβ * g dx ∧
       g ∈ GrSub Y embD dq0 dy0 ∧
       IsDivR (g dx) (g dβ) (g dq0) ∧
       IsDivR (g dv) (g dy) (g dA) ∧
       IsDivR (g dy) (g dy0) (g dB) ∧
       g dt = max (g dA) (g dB)}

/-! The fourteen named pieces of `DRatBody`. -/

def drP1 : Set (DRIdx k → ℝ) := {g | 0 < g dx}
def drP2 (Y : Set (Fin (k + 2) → ℝ)) : Set (DRIdx k → ℝ) := GrSub Y embD dx dy
def drP3 : Set (DRIdx k → ℝ) := {g | g dy ≠ 0}
def drP4 (Y : Set (Fin (k + 2) → ℝ)) : Set (DRIdx k → ℝ) := GrSub Y embD dz dy2
def drP5 : Set (DRIdx k → ℝ) := {g | g dz = 2 * g dx}
def drP6 : Set (DRIdx k → ℝ) := {g | g dw * g dy = g dy2}
def drP7 : Set (DRIdx k → ℝ) := {g | g dβ ≤ g dw ∨ g dw ≤ -g dβ}
def drP8 (Y : Set (Fin (k + 2) → ℝ)) : Set (DRIdx k → ℝ) := GrSub Y embD dz2 dv
def drP9 : Set (DRIdx k → ℝ) := {g | g dz2 = g dβ * g dx}
def drP10 (Y : Set (Fin (k + 2) → ℝ)) : Set (DRIdx k → ℝ) := GrSub Y embD dq0 dy0
def drP11 : Set (DRIdx k → ℝ) := {g | IsDivR (g dx) (g dβ) (g dq0)}
def drP12 : Set (DRIdx k → ℝ) := {g | IsDivR (g dv) (g dy) (g dA)}
def drP13 : Set (DRIdx k → ℝ) := {g | IsDivR (g dy) (g dy0) (g dB)}
def drP14 : Set (DRIdx k → ℝ) := {g | g dt = max (g dA) (g dB)}

/-- `DRatBody` is the Boolean combination of the fourteen pieces. -/
theorem DRatBody_eq_pieces {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) :
    DRatBody Y = drP1 ∩ drP2 Y ∩ drP3 ∩ drP4 Y ∩ drP5 ∩ drP6 ∩ drP7 ∩ drP8 Y ∩ drP9 ∩
      drP10 Y ∩ drP11 ∩ drP12 ∩ drP13 ∩ drP14 := by
  ext g
  simp only [DRatBody, drP1, drP2, drP3, drP4, drP5, drP6, drP7, drP8, drP9, drP10,
    drP11, drP12, drP13, drP14, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- `DRatBody` decoded: the body evaluated on the substitution `Sum.elim v u`. -/
theorem DRatBody_iff {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (v : Fin 2 → ℝ)
    (u : Fin k ⊕ Fin 11 → ℝ) :
    Sum.elim v u ∈ DRatBody Y ↔
      (0 < u (Sum.inr 0) ∧
       Gr Y (fun i => u (Sum.inl i)) (u (Sum.inr 0)) (u (Sum.inr 2)) ∧
       u (Sum.inr 2) ≠ 0 ∧
       Gr Y (fun i => u (Sum.inl i)) (u (Sum.inr 8)) (u (Sum.inr 3)) ∧
       u (Sum.inr 8) = 2 * u (Sum.inr 0) ∧
       u (Sum.inr 1) * u (Sum.inr 2) = u (Sum.inr 3) ∧
       (v 0 ≤ u (Sum.inr 1) ∨ u (Sum.inr 1) ≤ -v 0) ∧
       Gr Y (fun i => u (Sum.inl i)) (u (Sum.inr 9)) (u (Sum.inr 4)) ∧
       u (Sum.inr 9) = v 0 * u (Sum.inr 0) ∧
       Gr Y (fun i => u (Sum.inl i)) (u (Sum.inr 10)) (u (Sum.inr 5)) ∧
       IsDivR (u (Sum.inr 0)) (v 0) (u (Sum.inr 10)) ∧
       IsDivR (u (Sum.inr 4)) (u (Sum.inr 2)) (u (Sum.inr 6)) ∧
       IsDivR (u (Sum.inr 2)) (u (Sum.inr 5)) (u (Sum.inr 7)) ∧
       v 1 = max (u (Sum.inr 6)) (u (Sum.inr 7))) := by
  simp only [DRatBody, Set.mem_ofPred_eq, Set.mem_setOf_eq, grSub_embD, dc, dβ, dt, dx, dw,
    dy, dy2, dv, dy0, dA, dB, dz, dz2, dq0, embD, Sum.elim_inl, Sum.elim_inr, Fin.isValue]

/-! ## 3. The deepness atom -/

/-- The body of the *negation* of the deepness condition `IsDeepR B₀ c β x`: `b ∈ B₀`,
`q₁ = x/(2β)` and `q₁ ≤ b ≤ 2βx`.  The `Fin 2` block carries `(b, q₁)`. -/
def DeepBodyNeg {k : ℕ} (B₀ : Set (Fin (k + 1) → ℝ)) : Set (DRIdx k ⊕ Fin 2 → ℝ) :=
  {h | Fin.cons (h (Sum.inr (0 : Fin 2))) (fun i : Fin k => h (Sum.inl (dc i))) ∈ B₀ ∧
       IsDivR (h (Sum.inl dx)) (2 * h (Sum.inl dβ)) (h (Sum.inr (1 : Fin 2))) ∧
       h (Sum.inr (1 : Fin 2)) ≤ h (Sum.inr (0 : Fin 2)) ∧
       h (Sum.inr (0 : Fin 2)) ≤ 2 * h (Sum.inl dβ) * h (Sum.inl dx)}

/-- The universal projection of the deepness body. -/
def DRDeep {k : ℕ} (B₀ : Set (Fin (k + 1) → ℝ)) : Set (DRIdx k → ℝ) :=
  {g | ∀ u : Fin 2 → ℝ, Sum.elim g u ∉ DeepBodyNeg B₀}

/-- `g ∈ DRDeep B₀` is exactly the deepness of the fibre of `B₀` at `(dc, dβ, dx)`. -/
theorem mem_DRDeep_iff {k : ℕ} (B₀ : Set (Fin (k + 1) → ℝ)) (g : DRIdx k → ℝ) :
    g ∈ DRDeep B₀ ↔ IsDeepR B₀ (fun i => g (dc i)) (g dβ) (g dx) := by
  simp only [DRDeep, Set.mem_setOf_eq, DeepBodyNeg, IsDeepR, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h b hb hcon
    exact h ![b, g dx / (2 * g dβ)]
      ⟨hb, (isDivR_iff _ _ _).mpr rfl, hcon.1, hcon.2⟩
  · intro h u hcon
    rcases hcon with ⟨hb, hdiv, hle1, hle2⟩
    have hu : g dx / (2 * g dβ) ≤ u 0 := by
      have h1 : g dx / (2 * g dβ) = u 1 := (isDivR_iff _ _ _).mp hdiv
      linarith
    exact h (u 0) hb ⟨hu, hle2⟩

/-! ## 4. The graph of `DeepRatSet` -/

/-- The graph of the set-valued `DeepRatSet`: `(β, t) ↦` the membership `t ∈ DeepRatSet Y B₀ β`. -/
def DRg {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Set (Fin 2 → ℝ) :=
  {v | ∃ u : Fin k ⊕ Fin 11 → ℝ, Sum.elim v u ∈ (DRatBody Y ∩ DRDeep B₀)}

/-- `DRg` is the graph of `DeepRatSet`. -/
theorem mem_DRg_iff {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ))
    (v : Fin 2 → ℝ) :
    v ∈ DRg Y B₀ ↔ v 1 ∈ DeepRatSet Y B₀ (v 0) := by
  rw [DRg]
  constructor
  · rintro ⟨u, hbody, hdeep⟩
    rw [mem_DRDeep_iff] at hdeep
    rw [DRatBody_iff] at hbody
    obtain ⟨hpos, hYx, hne, hYz, hdz, hprod, habs, hYw, hdz2, hYq, hdiv0, hdivA, hdivB,
      hmax⟩ := hbody
    refine ⟨fun i => u (Sum.inl i), u (Sum.inr 0), u (Sum.inr 1), u (Sum.inr 2),
      u (Sum.inr 3), u (Sum.inr 4), u (Sum.inr 5), u (Sum.inr 6), u (Sum.inr 7),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hpos
    · simpa [Sum.elim_inl, Sum.elim_inr] using hdeep
    · exact hYx
    · exact hne
    · rw [← hdz]; exact hYz
    · exact hprod
    · exact habs
    · rw [← hdz2]; exact hYw
    · rw [(isDivR_iff _ _ _).mp hdiv0]; exact hYq
    · exact hdivA
    · exact hdivB
    · exact hmax
  · rintro ⟨c, x, w, y, y₂, v', y₀, A, B, hpos, hdeep, hYx, hne, hYz, hprod, habs, hYw,
      hYq, hdivA, hdivB, hmax⟩
    refine ⟨Sum.elim c ![x, w, y, y₂, v', y₀, A, B, 2 * x, v 0 * x, x / v 0], ?_, ?_⟩
    · rw [DRatBody_iff]
      refine ⟨hpos, ?_, hne, ?_, ?_, hprod, habs, ?_, ?_, hYq, ?_, hdivA, hdivB, hmax⟩
      · simpa using hYx
      · simpa using hYz
      · simp
      · simpa using hYw
      · simp
      · exact (isDivR_iff _ _ _).mpr rfl
    · rw [mem_DRDeep_iff]
      simpa [Sum.elim_inl, Sum.elim_inr] using hdeep

/-! ## 5. The lower-bound and glb graphs -/

/-- The graph of "`w 1` is a lower bound of `DeepRatSet Y B₀ (w 0)`". -/
def DRLower {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) :
    Set (Fin 2 → ℝ) :=
  {w | ∀ t : ℝ, ![w 0, t] ∈ DRg Y B₀ → w 1 ≤ t}

/-- The graph of "`v 1` is above every lower bound of `DeepRatSet Y B₀ (v 0)`". -/
def DRLUB {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) :
    Set (Fin 2 → ℝ) :=
  {v | ∀ c : ℝ, ![v 0, c] ∈ DRLower Y B₀ → c ≤ v 1}

theorem mem_DRLower_iff {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ))
    (w : Fin 2 → ℝ) :
    w ∈ DRLower Y B₀ ↔ ∀ t : ℝ, t ∈ DeepRatSet Y B₀ (w 0) → w 1 ≤ t := by
  simp only [DRLower, Set.mem_ofPred_eq, mem_DRg_iff, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one]

theorem mem_DRLUB_iff {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ))
    (v : Fin 2 → ℝ) :
    v ∈ DRLUB Y B₀ ↔
      ∀ c : ℝ, (∀ t : ℝ, t ∈ DeepRatSet Y B₀ (v 0) → c ≤ t) → c ≤ v 1 := by
  simp only [DRLUB, Set.mem_ofPred_eq, mem_DRLower_iff, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- `DeepThetaG` is the Boolean combination of the three clauses of the glb. -/
theorem DeepThetaG_eq {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) :
    DeepThetaG Y B₀ = {v : Fin 2 → ℝ | 1 ≤ v 0} ∩ DRLower Y B₀ ∩ DRLUB Y B₀ := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [mem_DRLower_iff, mem_DRLUB_iff]
  simp only [DeepThetaG, Set.mem_ofPred_eq, IsGLB, IsGreatest,
    lowerBounds, upperBounds]
  tauto

/-! ## 6. Definability of the lower-bound and glb graphs -/

/-- `DRLower` is `univ`-definable as soon as `DRg` is. -/
theorem DRLower_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hDRg : (Set.univ : Set ℝ).Definable LRc (DRg Y B₀)) :
    (Set.univ : Set ℝ).Definable LRc (DRLower Y B₀) := by
  have hpre : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin 1) → ℝ |
        g ∘ (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
          Fin 2 → Fin 2 ⊕ Fin 1) ∈ DRg Y B₀} :=
    hDRg.preimage_comp (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
      Fin 2 → Fin 2 ⊕ Fin 1)
  have hle : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin 1) → ℝ | g (Sum.inl 1) ≤ g (Sum.inr 0)} := by
    have h := definable_le_LRc (σ := Fin 2 ⊕ Fin 1) (MvPolynomial.X (Sum.inl (1 : Fin 2)))
      (MvPolynomial.X (Sum.inr (0 : Fin 1)))
    convert h using 1
    ext g
    simp [MvPolynomial.eval_X]
  have hS : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin 1) → ℝ |
        g ∘ (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
          Fin 2 → Fin 2 ⊕ Fin 1) ∈ DRg Y B₀ →
        g (Sum.inl 1) ≤ g (Sum.inr 0)} := by
    have h := hpre.compl.union hle
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  have h := hS.forall_of_finite (α := Fin 2) (β := Fin 1)
  have hset : {v : Fin 2 → ℝ | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈
        {g : (Fin 2 ⊕ Fin 1) → ℝ |
          g ∘ (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
            Fin 2 → Fin 2 ⊕ Fin 1) ∈ DRg Y B₀ →
          g (Sum.inl 1) ≤ g (Sum.inr 0)}} = DRLower Y B₀ := by
    ext v
    simp only [Set.mem_setOf_eq, DRLower, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Fin.isValue, Matrix.cons_val]
    constructor
    · intro hv t ht
      exact hv (fun _ => t) ht
    · intro hv u hu
      exact hv (u 0) hu
  rw [hset] at h
  exact h

/-- `DRLUB` is `univ`-definable as soon as `DRLower` is. -/
theorem DRLUB_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hLow : (Set.univ : Set ℝ).Definable LRc (DRLower Y B₀)) :
    (Set.univ : Set ℝ).Definable LRc (DRLUB Y B₀) := by
  have hpre : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin 1) → ℝ |
        g ∘ (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
          Fin 2 → Fin 2 ⊕ Fin 1) ∈ DRLower Y B₀} :=
    hLow.preimage_comp (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
      Fin 2 → Fin 2 ⊕ Fin 1)
  have hle : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin 1) → ℝ | g (Sum.inr 0) ≤ g (Sum.inl 1)} := by
    have h := definable_le_LRc (σ := Fin 2 ⊕ Fin 1) (MvPolynomial.X (Sum.inr (0 : Fin 1)))
      (MvPolynomial.X (Sum.inl (1 : Fin 2)))
    convert h using 1
    ext g
    simp [MvPolynomial.eval_X]
  have hS : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin 1) → ℝ |
        g ∘ (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
          Fin 2 → Fin 2 ⊕ Fin 1) ∈ DRLower Y B₀ →
        g (Sum.inr 0) ≤ g (Sum.inl 1)} := by
    have h := hpre.compl.union hle
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  have h := hS.forall_of_finite (α := Fin 2) (β := Fin 1)
  have hset : {v : Fin 2 → ℝ | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈
        {g : (Fin 2 ⊕ Fin 1) → ℝ |
          g ∘ (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
            Fin 2 → Fin 2 ⊕ Fin 1) ∈ DRLower Y B₀ →
          g (Sum.inr 0) ≤ g (Sum.inl 1)}} = DRLUB Y B₀ := by
    ext v
    simp only [Set.mem_setOf_eq, DRLUB, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Fin.isValue, Matrix.cons_val]
    constructor
    · intro hv t ht
      exact hv (fun _ => t) ht
    · intro hv u hu
      exact hv (u 0) hu
  rw [hset] at h
  exact h

end Work.WilC4
