/-
  WilC4/ClusterSelf/Sets : copy of `WilC4/ClusterSets` under the namespace `Work.WilC4.CESAux`.

  The witness set `Q1 k Y B₀` and the chain `Q1 → Q01 → Q0raw → Q0 → ClusterERfam` with the
  `∅`-definability of each step.  See `WilC4/ClusterER_definable_self.lean` for the rationale.
-/
import Mathlib
import Submission.Work.WilC4.ClusterSelf.Tool

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Work.WilC4.CESAux

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language

open WilkiesDesign WilkiesDesign.CG


/-! ## 1. The contexts -/

/-- The context `(ρ, β)`. -/
abbrev C2 : Type := Fin 1 ⊕ Fin 1

/-- The context `(ρ, β, c)`. -/
abbrev C3 (k : ℕ) : Type := (Fin 1 ⊕ Fin 1) ⊕ Fin k

/-- The context `(ρ, β, c, x)`. -/
abbrev C4 (k : ℕ) : Type := ((Fin 1 ⊕ Fin 1) ⊕ Fin k) ⊕ Fin 1

/-- The context `(ρ, β, c, x, b)`. -/
abbrev DB (k : ℕ) : Type := C4 k ⊕ Fin 1

/-- The context `(ρ, β, c, x, b, d)`. -/
abbrev DB2 (k : ℕ) : Type := DB k ⊕ Fin 1

/-- The context `(ρ, β, c, x, t, e, (y,y',τ,ω,ι))`. -/
abbrev TB (k : ℕ) : Type := ((C4 k ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 5

/-- The context `(ρ, β, c, x, t)` — the image of `TB` under the projection over the last two
blocks. -/
abbrev TA (k : ℕ) : Type := C4 k ⊕ Fin 1

/-- The context `(ρ, β, c, x, t, e)` — the image of `TB` under the projection over the last
block. -/
abbrev TE (k : ℕ) : Type := (C4 k ⊕ Fin 1) ⊕ Fin 1

/-! ## 2. The slots -/

/-! ### `C2`, `C3`, `C4` -/

/-- `ρ` in `C2`. -/
def r2 : C2 := Sum.inl (0 : Fin 1)

/-- `β` in `C2`. -/
def b2 : C2 := Sum.inr (0 : Fin 1)

/-- `ρ` in `C3`. -/
def r3 {k : ℕ} : C3 k := Sum.inl (r2 : C2)

/-- `β` in `C3`. -/
def b3 {k : ℕ} : C3 k := Sum.inl (b2 : C2)

/-- `c j` in `C3`. -/
def c3 {k : ℕ} (j : Fin k) : C3 k := Sum.inr j

/-- `ρ` in `C4`. -/
def r4 {k : ℕ} : C4 k := Sum.inl (r3 : C3 k)

/-- `β` in `C4`. -/
def b4 {k : ℕ} : C4 k := Sum.inl (b3 : C3 k)

/-- `c j` in `C4`. -/
def c4 {k : ℕ} (j : Fin k) : C4 k := Sum.inl (c3 j)

/-- `x` in `C4`. -/
def x4 {k : ℕ} : C4 k := Sum.inr (0 : Fin 1)

/-! ### `DB`, `DB2` -/

/-- `b` in `DB`. -/
def bD {k : ℕ} : DB k := Sum.inr (0 : Fin 1)

/-- `b` in `DB2`. -/
def bD2 {k : ℕ} : DB2 k := Sum.inl (bD : DB k)

/-- `d` in `DB2`. -/
def dD2 {k : ℕ} : DB2 k := Sum.inr (0 : Fin 1)

/-- `β` in `DB2`. -/
def b4D2 {k : ℕ} : DB2 k := Sum.inl (Sum.inl (b4 : C4 k))

/-- `x` in `DB2`. -/
def x4D2 {k : ℕ} : DB2 k := Sum.inl (Sum.inl (x4 : C4 k))

/-- `c j` in `DB2`. -/
def c4D2 {k : ℕ} (j : Fin k) : DB2 k := Sum.inl (Sum.inl (c4 j))

/-! ### `TA`, `TE`, `TB` -/

/-- `ρ` in `TA`. -/
def rA {k : ℕ} : TA k := Sum.inl (r4 : C4 k)

/-- `β` in `TA`. -/
def bA {k : ℕ} : TA k := Sum.inl (b4 : C4 k)

/-- `c j` in `TA`. -/
def cA {k : ℕ} (j : Fin k) : TA k := Sum.inl (c4 j)

/-- `x` in `TA`. -/
def xA {k : ℕ} : TA k := Sum.inl (x4 : C4 k)

/-- `t` in `TA`. -/
def tA {k : ℕ} : TA k := Sum.inr (0 : Fin 1)

/-- `ρ` in `TE`. -/
def rE {k : ℕ} : TE k := Sum.inl (rA : TA k)

/-- `β` in `TE`. -/
def bE {k : ℕ} : TE k := Sum.inl (bA : TA k)

/-- `c j` in `TE`. -/
def cE {k : ℕ} (j : Fin k) : TE k := Sum.inl (cA j)

/-- `x` in `TE`. -/
def xE {k : ℕ} : TE k := Sum.inl (xA : TA k)

/-- `t` in `TE`. -/
def tE {k : ℕ} : TE k := Sum.inl (tA : TA k)

/-- `e` in `TE`. -/
def eE {k : ℕ} : TE k := Sum.inr (0 : Fin 1)

/-- `ρ` in `TB`. -/
def rT {k : ℕ} : TB k := Sum.inl (Sum.inl (Sum.inl (r4 : C4 k)))

/-- `β` in `TB`. -/
def bT {k : ℕ} : TB k := Sum.inl (Sum.inl (Sum.inl (b4 : C4 k)))

/-- `c j` in `TB`. -/
def cT {k : ℕ} (j : Fin k) : TB k := Sum.inl (Sum.inl (Sum.inl (c4 j)))

/-- `x` in `TB`. -/
def xT {k : ℕ} : TB k := Sum.inl (Sum.inl (Sum.inl (x4 : C4 k)))

/-- `t` in `TB`. -/
def tT {k : ℕ} : TB k := Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))

/-- `e` in `TB`. -/
def eT {k : ℕ} : TB k := Sum.inl (Sum.inr (0 : Fin 1))

/-- `y` in `TB`. -/
def yT {k : ℕ} : TB k := Sum.inr (0 : Fin 5)

/-- `y'` in `TB`. -/
def yT' {k : ℕ} : TB k := Sum.inr (1 : Fin 5)

/-- `τ` in `TB`. -/
def tauT {k : ℕ} : TB k := Sum.inr (2 : Fin 5)

/-- `ω` in `TB`. -/
def omT {k : ℕ} : TB k := Sum.inr (3 : Fin 5)

/-- `ι` in `TB`. -/
def ioT {k : ℕ} : TB k := Sum.inr (4 : Fin 5)

/-! ## 3. `Gr` and `B₀` read off in a context -/

/-- `Gr Y c x y` read off in the context `ρ`: `x` at the slot `a`, `y` at the slot `b`, the
parameters `c` at the slots `cs`. -/
def GrS {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) {ρ : Type} (cs : Fin k → ρ) (a b : ρ) :
    Set (ρ → ℝ) :=
  {u | Fin.cons (u a) (Fin.cons (u b) (u ∘ cs)) ∈ Y}

/-- `Fin.cons b c ∈ B₀` read off in the context `ρ`. -/
def BS {k : ℕ} (B₀ : Set (Fin (k + 1) → ℝ)) {ρ : Type} (cs : Fin k → ρ) (b : ρ) :
    Set (ρ → ℝ) :=
  {u | Fin.cons (u b) (u ∘ cs) ∈ B₀}

theorem comp_cons_cons {k : ℕ} {ρ : Type} (u : ρ → ℝ) (a b : ρ) (ι : Fin k → ρ) :
    u ∘ (Fin.cons a (Fin.cons b ι)) = Fin.cons (u a) (Fin.cons (u b) (u ∘ ι)) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ l => rfl

theorem comp_cons {k : ℕ} {ρ : Type} (u : ρ → ℝ) (b : ρ) (ι : Fin k → ρ) :
    u ∘ (Fin.cons b ι) = Fin.cons (u b) (u ∘ ι) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

theorem GrS_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) {ρ : Type} (cs : Fin k → ρ) (a b : ρ) :
    (∅ : Set ℝ).Definable LRc (GrS Y cs a b) := by
  have h := hY.preimage_comp (Fin.cons a (Fin.cons b cs))
  have hset : GrS Y cs a b =
      (fun g : ρ → ℝ => g ∘ (Fin.cons a (Fin.cons b cs))) ⁻¹' Y := by
    ext u
    simp only [Set.mem_preimage, GrS, Set.mem_ofPred_eq, Set.mem_setOf_eq, comp_cons_cons]
  rw [hset]; exact h

theorem BS_definable {k : ℕ} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hB₀ : (∅ : Set ℝ).Definable LRc B₀) {ρ : Type} (cs : Fin k → ρ) (b : ρ) :
    (∅ : Set ℝ).Definable LRc (BS B₀ cs b) := by
  have h := hB₀.preimage_comp (Fin.cons b cs)
  have hset : BS B₀ cs b = (fun g : ρ → ℝ => g ∘ (Fin.cons b cs)) ⁻¹' B₀ := by
    ext u
    simp only [Set.mem_preimage, BS, Set.mem_ofPred_eq, Set.mem_setOf_eq, comp_cons]
  rw [hset]; exact h

/-! ## 4. The deepness bad set -/

/-- The bad condition of the deepness clause, in coordinates: the breakpoint `b` of `B₀` lies in
the forbidden window `[x/(2β), 2βx]` (`d` names `x/(2β)`, so the first half is `d ≤ b`). -/
def DeepP (k : ℕ) (B₀ : Set (Fin (k + 1) → ℝ)) (β x : ℝ) (c : Fin k → ℝ) (b d : ℝ) : Prop :=
  Fin.cons b c ∈ B₀ ∧ (β + β) * d = x ∧ d ≤ b ∧ b ≤ (β + β) * x

/-- The bad set of the deepness clause in the context `(ρ,β,c,x,b,d)`. -/
def DeepBad (k : ℕ) (B₀ : Set (Fin (k + 1) → ℝ)) : Set (DB2 k → ℝ) :=
  {w | DeepP k B₀ (w b4D2) (w x4D2) (fun j => w (c4D2 j)) (w bD2) (w dD2)}

theorem DeepBad_definable (k : ℕ) {B₀ : Set (Fin (k + 1) → ℝ)}
    (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (∅ : Set ℝ).Definable LRc (DeepBad k B₀) := by
  have h1 : (∅ : Set ℝ).Definable LRc
      {w : DB2 k → ℝ | Fin.cons (w bD2) (w ∘ c4D2) ∈ B₀} := BS_definable hB₀ c4D2 bD2
  have h2 : (∅ : Set ℝ).Definable LRc
      {w : DB2 k → ℝ | (w b4D2 + w b4D2) * w dD2 = w x4D2} := by
    have h := definable_eq_fun (ρ := DB2 k)
      (defFun_ringTerm (((Term.var b4D2) + (Term.var b4D2)) * (Term.var dD2) :
        Language.ring.Term (DB2 k)))
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := x4D2))
    simpa using h
  have h3 : (∅ : Set ℝ).Definable LRc {w : DB2 k → ℝ | w dD2 ≤ w bD2} := by
    have h := definable_le_fun (ρ := DB2 k)
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := dD2))
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := bD2))
    simpa using h
  have h4 : (∅ : Set ℝ).Definable LRc
      {w : DB2 k → ℝ | w bD2 ≤ (w b4D2 + w b4D2) * w x4D2} := by
    have h := definable_le_fun (ρ := DB2 k)
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := bD2))
      (defFun_ringTerm (((Term.var b4D2) + (Term.var b4D2)) * (Term.var x4D2) :
        Language.ring.Term (DB2 k)))
    simpa using h
  convert ((h1.inter h2).inter h3).inter h4 using 1
  ext w
  simp only [DeepBad, DeepP, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_setOf_eq]
  tauto

/-- The projection of `DeepBad` over the auxiliary variable `d = x/(2β)`: `b` is a breakpoint
with `x/(2β) ≤ b`. -/
def DeepBad1 (k : ℕ) (B₀ : Set (Fin (k + 1) → ℝ)) : Set (DB k → ℝ) :=
  {v | ∃ d : Fin 1 → ℝ, Sum.elim v d ∈ DeepBad k B₀}

theorem DeepBad1_definable (k : ℕ) {B₀ : Set (Fin (k + 1) → ℝ)}
    (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (∅ : Set ℝ).Definable LRc (DeepBad1 k B₀) :=
  (DeepBad_definable k hB₀).exists_of_finite (α := DB k) (β := Fin 1)

/-- The set of `(ρ,β,c,x)` for which `x` is deep: no breakpoint of the fibre `B₀` at the
parameter `c` lies in `[x/(2β), 2βx]` (the first half written with an auxiliary variable). -/
def Sdeep (k : ℕ) (B₀ : Set (Fin (k + 1) → ℝ)) : Set (C4 k → ℝ) :=
  {u | ∀ b : Fin 1 → ℝ, Sum.elim u b ∉ DeepBad1 k B₀}

theorem Sdeep_definable (k : ℕ) {B₀ : Set (Fin (k + 1) → ℝ)}
    (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (∅ : Set ℝ).Definable LRc (Sdeep k B₀) :=
  (DeepBad1_definable k hB₀).compl.forall_of_finite (α := C4 k) (β := Fin 1)

/-! ## 5. The ratio bad set -/

/-- The bad condition of the ratio clause, in coordinates.  `e` names `x/β`, `τ` names `2t`,
`ω` names `y'/y` and `ι` names `1/β`; the clause says that `t` lies in the window
`[x/β, xβ]`, that `y` and `y'` are values of the fibre at `t` and `2t`, that `y ≠ 0`, and that
the ratio is *not* within `1/β` of `ρ`. -/
def BadP (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) (ρ β x : ℝ) (c : Fin k → ℝ)
    (e t τ y y' ω ι : ℝ) : Prop :=
  β * e = x ∧ e ≤ t ∧ t ≤ x * β ∧ τ = t + t ∧
  Fin.cons t (Fin.cons y c) ∈ Y ∧ Fin.cons τ (Fin.cons y' c) ∈ Y ∧
  y * ω = y' ∧ β * ι = 1 ∧ y ≠ 0 ∧ ¬(|ω - ρ| ≤ ι)

/-- The bad set of the ratio clause in the context `(ρ,β,c,x,t,e,(y,y',τ,ω,ι))`. -/
def BadR (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) : Set (TB k → ℝ) :=
  {w | BadP k Y (w rT) (w bT) (w xT) (fun j => w (cT j)) (w eT) (w tT) (w tauT)
        (w yT) (w yT') (w omT) (w ioT)}

theorem BadR_definable (k : ℕ) {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (BadR k Y) := by
  have h1 : (∅ : Set ℝ).Definable LRc {w : TB k → ℝ | w bT * w eT = w xT} := by
    have h := definable_eq_fun (ρ := TB k)
      (defFun_ringTerm ((Term.var bT) * (Term.var eT) : Language.ring.Term (TB k)))
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := xT))
    simpa using h
  have h2 : (∅ : Set ℝ).Definable LRc {w : TB k → ℝ | w eT ≤ w tT} := by
    have h := definable_le_fun (ρ := TB k)
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := eT))
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := tT))
    simpa using h
  have h3 : (∅ : Set ℝ).Definable LRc {w : TB k → ℝ | w tT ≤ w xT * w bT} := by
    have h := definable_le_fun (ρ := TB k)
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := tT))
      (defFun_ringTerm ((Term.var xT) * (Term.var bT) : Language.ring.Term (TB k)))
    simpa using h
  have h4 : (∅ : Set ℝ).Definable LRc {w : TB k → ℝ | w tauT = w tT + w tT} := by
    have h := definable_eq_fun (ρ := TB k)
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := tauT))
      (defFun_ringTerm ((Term.var tT) + (Term.var tT) : Language.ring.Term (TB k)))
    simpa using h
  have h5 : (∅ : Set ℝ).Definable LRc
      {w : TB k → ℝ | Fin.cons (w tT) (Fin.cons (w yT) (w ∘ cT)) ∈ Y} :=
    GrS_definable hY cT tT yT
  have h6 : (∅ : Set ℝ).Definable LRc
      {w : TB k → ℝ | Fin.cons (w tauT) (Fin.cons (w yT') (w ∘ cT)) ∈ Y} :=
    GrS_definable hY cT tauT yT'
  have h7 : (∅ : Set ℝ).Definable LRc {w : TB k → ℝ | w yT * w omT = w yT'} := by
    have h := definable_eq_fun (ρ := TB k)
      (defFun_ringTerm ((Term.var yT) * (Term.var omT) : Language.ring.Term (TB k)))
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := yT'))
    simpa using h
  have h8 : (∅ : Set ℝ).Definable LRc {w : TB k → ℝ | w bT * w ioT = 1} := by
    have h := definable_eq_fun (ρ := TB k)
      (defFun_ringTerm ((Term.var bT) * (Term.var ioT) : Language.ring.Term (TB k)))
      (defFun_const (ρ := TB k) 1)
    simpa using h
  have h9 : (∅ : Set ℝ).Definable LRc {w : TB k → ℝ | w yT ≠ 0} := by
    have h := definable_ne_fun (ρ := TB k)
      (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := yT))
      (defFun_const (ρ := TB k) 0)
    simpa using h
  have h10 : (∅ : Set ℝ).Definable LRc {w : TB k → ℝ | ¬(|w omT - w rT| ≤ w ioT)} := by
    have hA : (∅ : Set ℝ).Definable LRc {w : TB k → ℝ | -(w ioT) ≤ w omT - w rT} := by
      have h := definable_le_fun (ρ := TB k)
        (defFun_neg (ρ := TB k) ioT)
        (defFun_sub (ρ := TB k) omT rT)
      simpa using h
    have hB : (∅ : Set ℝ).Definable LRc {w : TB k → ℝ | w omT - w rT ≤ w ioT} := by
      have h := definable_le_fun (ρ := TB k)
        (defFun_sub (ρ := TB k) omT rT)
        (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := ioT))
      simpa using h
    have h := (hA.inter hB).compl
    convert h using 1
    ext w
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_setOf_eq,
      abs_le]
  have h := (((((((((h1.inter h2).inter h3).inter h4).inter h5).inter h6).inter h7).inter
    h8).inter h9).inter h10)
  convert h using 1
  ext w
  simp only [BadR, BadP, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_setOf_eq]
  tauto

/-- The projection of `BadR` over the five auxiliaries `(y,y',τ,ω,ι)`. -/
def BadR1 (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) : Set (TE k → ℝ) :=
  {v | ∃ w : Fin 5 → ℝ, Sum.elim v w ∈ BadR k Y}

theorem BadR1_definable (k : ℕ) {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (BadR1 k Y) :=
  (BadR_definable k hY).exists_of_finite (α := TE k) (β := Fin 5)

/-- The projection of `BadR1` over the auxiliary `e = x/β`. -/
def BadR2 (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) : Set (TA k → ℝ) :=
  {v | ∃ e : Fin 1 → ℝ, Sum.elim v e ∈ BadR1 k Y}

theorem BadR2_definable (k : ℕ) {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (BadR2 k Y) :=
  (BadR1_definable k hY).exists_of_finite (α := TA k) (β := Fin 1)

/-- The set of `(ρ,β,c,x)` for which the ratio clause holds on the whole window `[x/β, xβ]`: no
`t` admits a bad pair of values. -/
def Srat (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) : Set (C4 k → ℝ) :=
  {u | ∀ t : Fin 1 → ℝ, Sum.elim u t ∉ BadR2 k Y}

theorem Srat_definable (k : ℕ) {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (Srat k Y) :=
  (BadR2_definable k hY).compl.forall_of_finite (α := C4 k) (β := Fin 1)

/-! ## 6. The witness set and the top of the chain -/

/-- `0 < x`. -/
def Spos (k : ℕ) : Set (C4 k → ℝ) := {u | 0 < u x4}

theorem Spos_definable (k : ℕ) : (∅ : Set ℝ).Definable LRc (Spos k) := by
  have h := definable_lt_fun (ρ := C4 k)
    (defFun_const (ρ := C4 k) 0)
    (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := x4))
  simpa [Spos] using h

/-- The witness set: `(ρ,β,c,x)` with `0 < x`, deepness and the ratio clause. -/
def Q1 (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Set (C4 k → ℝ) :=
  Spos k ∩ (Sdeep k B₀ ∩ Srat k Y)

theorem Q1_definable (k : ℕ) {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (∅ : Set ℝ).Definable LRc (Q1 k Y B₀) :=
  (Spos_definable k).inter ((Sdeep_definable k hB₀).inter (Srat_definable k hY))

/-- Eliminate `x`. -/
def Q01 (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Set (C3 k → ℝ) :=
  {v | ∃ x : Fin 1 → ℝ, Sum.elim v x ∈ Q1 k Y B₀}

theorem Q01_definable (k : ℕ) {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (∅ : Set ℝ).Definable LRc (Q01 k Y B₀) :=
  (Q1_definable k hY hB₀).exists_of_finite (α := C3 k) (β := Fin 1)

/-- Eliminate `c`. -/
def Q0raw (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Set (C2 → ℝ) :=
  {v | ∃ c : Fin k → ℝ, Sum.elim v c ∈ Q01 k Y B₀}

theorem Q0raw_definable (k : ℕ) {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (∅ : Set ℝ).Definable LRc (Q0raw k Y B₀) :=
  (Q01_definable k hY hB₀).exists_of_finite (α := C2) (β := Fin k)

/-- `0 < β`. -/
def Sbeta : Set (C2 → ℝ) := {v | 0 < v b2}

theorem Sbeta_definable : (∅ : Set ℝ).Definable LRc Sbeta := by
  have h := definable_lt_fun (ρ := C2)
    (defFun_const (ρ := C2) 0)
    (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := b2))
  simpa [Sbeta] using h

/-- The condition `0 < β → ∃ c x, (witness)`. -/
def Q0 (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Set (C2 → ℝ) :=
  Sbetaᶜ ∪ Q0raw k Y B₀

theorem Q0_definable (k : ℕ) {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (∅ : Set ℝ).Definable LRc (Q0 k Y B₀) :=
  (Sbeta_definable.compl).union (Q0raw_definable k hY hB₀)

/-- Quantify `β` universally: the set of `ρ` whose every scale `β > 0` carries a witness. -/
def ClusterERfam (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) :
    Set (Fin 1 → ℝ) :=
  {v | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈ Q0 k Y B₀}

theorem ClusterERfam_definable (k : ℕ) {Y : Set (Fin (k + 2) → ℝ)}
    {B₀ : Set (Fin (k + 1) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (∅ : Set ℝ).Definable LRc (ClusterERfam k Y B₀) :=
  (Q0_definable k hY hB₀).forall_of_finite (α := Fin 1) (β := Fin 1)


end Work.WilC4.CESAux
