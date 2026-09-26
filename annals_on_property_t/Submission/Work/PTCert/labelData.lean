import Submission.Work.PTCert.Glue3

/-!
# PTCert — data for `labelIdentity`

Definitions used by `Work.PTCert.labelIdentity` (the label identity of a certificate) and by the
lemmas it delegates.

The element assembled from a certificate's terms is
`(1/SCv) • K - targetSum q Dq + residualSum res (SCv·Dq)` where
* `K = Σ_{r<18} Σ_{g<ngE r} (multE (keyOf r g) · pv (keyOf r g)) • of (lprod 5 (keyWord r g))`,
* `targetSum q Dq = Σ_{p<6561} (q p / Dq) • of (lprod 5 [invL (p/81), p%81, 0, 0])`,
* `residualSum res den = Σ_{c<ncls} (res c / den / 2) • (of (lprod 5 (canonW c)) + of (lprod 5 (canonW c))⁻¹)`.

This note is proved by the labelled-sum principle (`labelPrinciple`) applied to the single sum
`Σ_{t : TIdx} tCoef t • of (tElt t)` (see `sumDecomp`), where every term carries a label
`tLab t` and a conjugator `σ ∈ Sg = SigmaSet 5` with `σ * tElt t * σ⁻¹ = labRep (tLab t)`
(`conjWitness`, straight from `ClassSem`).

The per-label coefficient sums are the pieces:
* keys (label `gcls k`, `k = keyOf r g`): `(1/SCv) · Σ_{k ∈ klist l} multE k · pv k` (`keyFiberSum`);
* targets (label `tcls p`): `-(1/Dq) · Σ_{p ∈ tlist l} q p` (`tgtFiberSum`);
* residual classes: `res l / (SCv·Dq)` (`resFiberSum`).

Their sum is `(Dq · Σ_{klist l} multE·pv - SCv · Σ_{tlist l} q + res l)/(SCv·Dq) = 0`
by the class-sum hypothesis `hcs` of `LabelIdentity`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

namespace Work.PTCert.LabelData

open Submission.PTCert Submission.PTCert.G
open Submission.PTCert.D
open scoped BigOperators

/-- The index type of the labelled decomposition of a certificate: the group keys `(r, g)`
(`r < 18`, `g < ngE r`), the target pairs `p < 6561`, and the two signs `±` of the residual
classes `c < ncls`. -/
abbrev TIdx : Type := (Σ r : Fin 18, Fin (ngE r.1)) ⊕ Fin 6561 ⊕ (Fin ncls × Bool)

/-- The group element of a term. -/
def tElt : TIdx → G5
  | Sum.inl t => lprod 5 (keyWord t.1.1 t.2.1)
  | Sum.inr (Sum.inl p) => lprod 5 [invL (p.1 / 81), p.1 % 81, 0, 0]
  | Sum.inr (Sum.inr (c, b)) =>
      if b then (lprod 5 (canonW c.1))⁻¹ else lprod 5 (canonW c.1)

/-- The coefficient of a term.  Residual terms carry the factor `1/2` so that the two signs of a
class add up to `res c / (SCv · Dq)`. -/
def tCoef (pv q res : ℕ → ℤ) (SCv Dq : ℤ) : TIdx → ℝ
  | Sum.inl t => (1 / (SCv : ℝ)) * ((multE (keyOf t.1.1 t.2.1) : ℝ) * (pv (keyOf t.1.1 t.2.1) : ℝ))
  | Sum.inr (Sum.inl p) => -((q p.1 : ℝ) / (Dq : ℝ))
  | Sum.inr (Sum.inr (c, _)) => (res c.1 : ℝ) / ((SCv : ℝ) * (Dq : ℝ)) / 2

/-- The label of a term. -/
def tLab : TIdx → ℕ
  | Sum.inl t => gcls (keyOf t.1.1 t.2.1)
  | Sum.inr (Sum.inl p) => tcls p.1
  | Sum.inr (Sum.inr (c, b)) => if b then icls c.1 else c.1

/-- The representative element of a label. -/
def labRep (l : ℕ) : G5 := lprod 5 (canonW l)

/-! ## The data facts of `ClassSem`, one by one -/

theorem ngL_length (hC : ClassSem) : ngL.length = 18 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := hC; exact h

theorem klist_length (hC : ClassSem) : klist.length = ncls := by
  obtain ⟨-, -, -, -, h, -, -, -, -, -, -, -⟩ := hC; exact h

theorem tlist_length (hC : ClassSem) : tlist.length = ncls := by
  obtain ⟨-, -, -, -, -, h, -, -, -, -, -, -⟩ := hC; exact h

theorem klist_flatten_perm (hC : ClassSem) : klist.flatten.Perm (allKeys ngL) := by
  obtain ⟨-, -, -, -, -, -, h, -, -, -, -, -⟩ := hC; exact h

theorem tlist_flatten_perm (hC : ClassSem) : tlist.flatten.Perm (List.range 6561) := by
  obtain ⟨-, -, -, -, -, -, -, h, -, -, -, -⟩ := hC; exact h

theorem klist_gcls (hC : ClassSem) : ∀ c < ncls, ∀ k ∈ klist.getD c [], gcls k = c := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -, -, -⟩ := hC; exact h

theorem tlist_tcls (hC : ClassSem) : ∀ c < ncls, ∀ p ∈ tlist.getD c [], tcls p = c := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -, -⟩ := hC; exact h

theorem gcls_lt (hC : ClassSem) {r g : ℕ} (hr : r < 18) (hg : g < ngE r) :
    gcls (keyOf r g) < ncls := (hC.2.1 r hr g hg).1

theorem key_conj (hC : ClassSem) {r g : ℕ} (hr : r < 18) (hg : g < ngE r) :
    ∃ σ ∈ Sg, σ * lprod 5 (keyWord r g) * σ⁻¹ = lprod 5 (canonW (gcls (keyOf r g))) :=
  (hC.2.1 r hr g hg).2

theorem tcls_lt (hC : ClassSem) {p : ℕ} (hp : p < 6561) : tcls p < ncls :=
  (hC.2.2.1 p hp).1

theorem tgt_conj (hC : ClassSem) {p : ℕ} (hp : p < 6561) :
    ∃ σ ∈ Sg, σ * lprod 5 [invL (p / 81), p % 81, 0, 0] * σ⁻¹
      = lprod 5 (canonW (tcls p)) := (hC.2.2.1 p hp).2

theorem icls_lt (hC : ClassSem) {c : ℕ} (hc : c < ncls) : icls c < ncls :=
  (hC.2.2.2.1 c hc).1

theorem res_conj (hC : ClassSem) {c : ℕ} (hc : c < ncls) :
    ∃ σ ∈ Sg, σ * (lprod 5 (canonW c))⁻¹ * σ⁻¹ = lprod 5 (canonW (icls c)) :=
  (hC.2.2.2.1 c hc).2

/-- The numbers `ngE r = ngL.getD r 0` of the rank-5 data are all `< 2048`, so that the key
`keyOf r g = 2048 r + g` determines the pair `(r, g)` whenever `g < ngE r`. -/
theorem ngE_lt_all : ∀ r : Fin 18, ngE r.1 < 2048 := by decide

theorem ngE_lt (r : Fin 18) : ngE r.1 < 2048 := ngE_lt_all r

theorem ngE_lt' {r : ℕ} (hr : r < 18) : ngE r < 2048 := ngE_lt ⟨r, hr⟩

/-- **Injectivity of the group key** on the range of the certificate's keys. -/
theorem keyOf_inj {r r' g g' : ℕ} (hr : r < 18) (hr' : r' < 18)
    (hg : g < ngE r) (hg' : g' < ngE r') (h : keyOf r g = keyOf r' g') : r = r' ∧ g = g' := by
  have h1 : ngE r < 2048 := ngE_lt' hr
  have h2 : ngE r' < 2048 := ngE_lt' hr'
  unfold keyOf at h
  omega

/-- **The keys of the certificate are the list `allKeys ngL`.** -/
theorem mem_allKeys (hC : ClassSem) {k : ℕ} :
    k ∈ allKeys ngL ↔ ∃ r < 18, ∃ g < ngE r, k = keyOf r g := by
  have hlen : ngL.length = 18 := ngL_length hC
  unfold allKeys
  rw [hlen, List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, hg⟩
    rw [List.mem_map] at hg
    obtain ⟨g, hg, rfl⟩ := hg
    rw [List.mem_range] at hr hg
    exact ⟨r, hr, g, hg, rfl⟩
  · rintro ⟨r, hr, g, hg, rfl⟩
    refine ⟨r, List.mem_range.mpr hr, ?_⟩
    rw [List.mem_map]
    exact ⟨g, List.mem_range.mpr hg, rfl⟩

end Work.PTCert.LabelData

end
