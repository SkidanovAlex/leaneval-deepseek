import Mathlib
import Submission.Work.RPA3.Defs
import Submission.Work.RPA3.Symp

/-!
# RPA3: the symplectic orthogonal of a Lagrangian plane is the plane itself

Let `Λ = span{u,v} ⊆ PS = ℝ⁴` be a Lagrangian plane: `u, v` are linearly independent and
`ω(u,v) = 0`.  Then every `w` which is `ω`-orthogonal to `u` and to `v` already lies in `Λ`:
`Λ^{⊥ω} = Λ`.

The proof here is the elementary one.  The Euclidean inner product `⟪a,b⟫ = ω(a, Jb)` of `PS`
satisfies `ω(Ja,b) = -⟪a,b⟫`; writing `w = a u + b v + c Ju + d Jv` (legitimate because
`u, v, Ju, Jv` are linearly independent and `finrank ℝ PS = 4`), the two orthogonality
hypotheses say, for `z = c u + d v ∈ Λ`, that `⟪z,u⟫ = 0` and `⟪z,v⟫ = 0`.  Hence
`⟪z,z⟫ = c⟪z,u⟫ + d⟪z,v⟫ = 0`, so `z = 0`, and by independence of `u, v` we get `c = d = 0`.
Thus `w = a u + b v`.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-- The standard Euclidean inner product of `PS = ℝ⁴`, in the same coordinates as `symp`; it is
the form `⟪a,b⟫ = ω(a, Jb)`. -/
def ip (a b : PS) : ℝ := a.1.1 * b.1.1 + a.1.2 * b.1.2 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- `⟪a,b⟫ = ω(a, Jb)`. -/
theorem ip_eq_symp (a b : PS) : ip a b = symp a (J b) := by rw [ip, symp_J_apply]

/-- `ω(Ja,b) = -⟪a,b⟫`. -/
theorem symp_J_left (a b : PS) : symp (J a) b = -ip a b := by
  rw [symp_J_apply', ← ip_eq_symp]

/-- The inner product is symmetric. -/
theorem ip_comm (a b : PS) : ip a b = ip b a := by simp only [ip]; ring

/-- `⟪a,a⟫ ≥ 0`. -/
theorem ip_self_nonneg (a : PS) : 0 ≤ ip a a := by
  rw [ip_eq_symp, symp_J_self]
  nlinarith [sq_nonneg a.1.1, sq_nonneg a.1.2, sq_nonneg a.2.1, sq_nonneg a.2.2]

/-- The inner product is positive definite: `⟪a,a⟫ = 0 ↔ a = 0`. -/
theorem ip_self_eq_zero_iff (a : PS) : ip a a = 0 ↔ a = 0 := by
  rw [ip_eq_symp]; exact symp_J_self_eq_zero_iff a

/-- Expansion of `ω(w, x)` when `w = a x + b y + c Jx + d Jy`: only the `Jx, Jy` part contributes,
and `ω(Jx,x) = -⟪x,x⟫`, `ω(Jy,x) = -⟪y,x⟫`. -/
theorem symp_expand_left (x y : PS) (hxy : symp x y = 0) (a b c d : ℝ) :
    symp (a • x + b • y + c • J x + d • J y) x = -(c * ip x x + d * ip y x) := by
  have h1 : symp (a • x + b • y + c • J x + d • J y) x
      = symp (a • x + b • y) x + symp (c • J x + d • J y) x := by
    rw [add_assoc, symp_add_left]
  have h2 : symp (a • x + b • y) x = 0 := by
    rw [symp_add_left, symp_smul_left, symp_smul_left, symp_self, mul_zero,
      symp_antisymm, hxy, neg_zero, mul_zero, add_zero]
  have h3 : symp (c • J x + d • J y) x = -(c * ip x x + d * ip y x) := by
    rw [symp_add_left, symp_smul_left, symp_smul_left, symp_J_left, symp_J_left]; ring
  rw [h1, h2, h3, zero_add]

/-- Expansion of `ω(w, y)` when `w = a x + b y + c Jx + d Jy`, cf. `symp_expand_left`. -/
theorem symp_expand_right (x y : PS) (hxy : symp x y = 0) (a b c d : ℝ) :
    symp (a • x + b • y + c • J x + d • J y) y = -(c * ip x y + d * ip y y) := by
  have h1 : symp (a • x + b • y + c • J x + d • J y) y
      = symp (a • x + b • y) y + symp (c • J x + d • J y) y := by
    rw [add_assoc, symp_add_left]
  have h2 : symp (a • x + b • y) y = 0 := by
    rw [symp_add_left, symp_smul_left, symp_smul_left, symp_self, mul_zero, hxy, mul_zero,
      add_zero]
  have h3 : symp (c • J x + d • J y) y = -(c * ip x y + d * ip y y) := by
    rw [symp_add_left, symp_smul_left, symp_smul_left, symp_J_left, symp_J_left]; ring
  rw [h1, h2, h3, zero_add]

/-- For a Lagrangian plane `Λ = span{u,v}` (with `u, v` independent and `ω(u,v) = 0`), a vector
`w` whose `ω`-pairings with `u` and with `v` both vanish is a combination of `u` and `v`, i.e. the
symplectic orthogonal of a Lagrangian plane is the plane itself.

Proof: `symp w u = 0` and `symp w v = 0` say that `w` pairs to zero with everything in
`span{u,v}`, i.e. `w ∈ (span{u,v})^⊥ω`; on the other hand `span{u,v} ⊆ (span{u,v})^⊥ω` since
`ω(u,v) = ω(u,u) = ω(v,v) = 0`, and both are 2-dimensional in the 4-dimensional `PS`, so they are
equal.  (Equivalently: `ω(Ja,b) = -⟪a,b⟫` so `Jw ⊥ span{u,v}` and `Jw ∈ J(span{u,v})` by dimension
counting.)  `Symp.lean` has the bilinearity and the inner-product identities. -/
theorem lagrangian_orthogonal (u v : Work.RPA3.PS)
    (huv : ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0) (hlag : Work.RPA3.symp u v = 0) :
    ∀ w : Work.RPA3.PS, Work.RPA3.symp w u = 0 → Work.RPA3.symp w v = 0 →
      ∃ a b : ℝ, w = a • u + b • v := by
  intro w hwu hwv
  -- `u, v, Ju, Jv` are linearly independent, hence a basis of the 4-dimensional `PS`.
  have hLI : LinearIndependent ℝ ![u, v, J u, J v] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : g 0 • u + g 1 • v + g 2 • J u + g 3 • J v = 0 := by
      have h' : ∑ i, g i • ![u, v, J u, J v] i = 0 := hg
      rw [Fin.sum_univ_four] at h'
      simpa using h'
    obtain ⟨h0, h1, h2, h3⟩ :=
      lagrangian_independent u v huv hlag (g 0) (g 1) (g 2) (g 3) hsum
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hfin : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range ![u, v, J u, J v])) = 4 := by
    rw [finrank_span_eq_card hLI]; simp
  have htop : Submodule.span ℝ (Set.range ![u, v, J u, J v]) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hfin]; simp [PS, Module.finrank_prod, Module.finrank_self]
  have hmem : w ∈ Submodule.span ℝ (Set.range ![u, v, J u, J v]) := by
    rw [htop]; exact Submodule.mem_top
  -- coefficients of `w` in the basis `u, v, Ju, Jv`
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hg' : g 0 • u + g 1 • v + g 2 • J u + g 3 • J v = w := by
    simpa [Fin.sum_univ_four] using hg
  -- the orthogonality hypotheses, in terms of `z = g 2 • u + g 3 • v`
  have he1 : g 2 * ip u u + g 3 * ip v u = 0 := by
    have h1 : symp w u = -(g 2 * ip u u + g 3 * ip v u) := by
      rw [← hg', symp_expand_left u v hlag]
    rw [hwu] at h1; linarith
  have he2 : g 2 * ip u v + g 3 * ip v v = 0 := by
    have h1 : symp w v = -(g 2 * ip u v + g 3 * ip v v) := by
      rw [← hg', symp_expand_right u v hlag]
    rw [hwv] at h1; linarith
  -- hence `⟪z,z⟫ = g 2 * ⟪z,u⟫ + g 3 * ⟪z,v⟫ = 0`
  have hz : g 2 • u + g 3 • v = 0 := by
    refine (ip_self_eq_zero_iff _).mp ?_
    have expand : ip (g 2 • u + g 3 • v) (g 2 • u + g 3 • v)
        = g 2 * (g 2 * ip u u + g 3 * ip v u) + g 3 * (g 2 * ip u v + g 3 * ip v v) := by
      simp only [ip, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      ring
    rw [expand, he1, he2]; ring
  -- independence of `u, v` kills the remaining coefficients
  obtain ⟨hg2, hg3⟩ := huv (g 2) (g 3) hz
  refine ⟨g 0, g 1, ?_⟩
  rw [← hg', hg2, hg3]
  simp

end Work.RPA3
