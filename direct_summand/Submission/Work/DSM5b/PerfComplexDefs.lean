import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.perfChartRing_pow_p_mem_iff

/-!
# DSM5b — the explicit (concrete) perfected chart Čech complex `PC`

This file contains the *concrete* data used by the proof of `Work.DSM5b.perfectedRootKilling`:

* `tupRng τ` — the finset of values of a tuple `τ : Fin (m+1) → ι`;
* `tupDel i τ = τ ∘ Fin.succAbove i` — the tuple with the `i`-th entry deleted;
* `tupIns k σ = Fin.cons k σ` — the tuple with `k` prepended;
* `rho p t h : perfChartRing p t S →ₐ[R] perfChartRing p t T` for `h : S ⊆ T` — the localisation
  map between perfected chart rings (restriction of `locRes`);
* `PCX p t m = ∀ τ : Fin (m+1) → ι, perfChartRing p t (tupRng τ)` — the terms of the explicit
  complex, and

  `PCd p t m : PCX p t m →ₗ[R] PCX p t (m+1)`, `(PCd z) τ = ∑ i, (-1)^i • rho (z (tupDel i τ))`

  — the alternating coface differential, written in coordinates.

The point of these definitions is that the *analysis* of the perfected chart Čech complex of
`DSMap.Mix2` (`K = (cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)`) can be split off
as a single identification statement (see `Submission/Work/DSM5b/CechIso.lean`), after which all the
homological algebra and all the Frobenius bookkeeping happens on `PCX`/`PCd` — where the differential
is an explicit formula and no `CategoryTheory` unfolding is needed.

Do NOT use the frozen sorried declaration `DSMap.Mix2.area_M5b`.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section Defs

variable {ι : Type a} [DecidableEq ι]

/-- The finset of values of a tuple `τ : Fin (m+1) → ι`. -/
def tupRng {m : ℕ} (τ : Fin (m + 1) → ι) : Finset ι := Finset.univ.image τ

/-- The tuple with the `i`-th entry deleted (`i : Fin (m+2)`). -/
def tupDel {m : ℕ} (i : Fin (m + 2)) (τ : Fin (m + 2) → ι) : Fin (m + 1) → ι :=
  τ ∘ Fin.succAbove i

/-- The tuple with `k` prepended. -/
def tupIns (k : ι) {m : ℕ} (σ : Fin (m + 1) → ι) : Fin (m + 2) → ι := Fin.cons k σ

@[simp] lemma tupDel_apply {m : ℕ} (i : Fin (m + 2)) (τ : Fin (m + 2) → ι)
    (b : Fin (m + 1)) : tupDel i τ b = τ (Fin.succAbove i b) := rfl

@[simp] lemma tupIns_zero (k : ι) {m : ℕ} (σ : Fin (m + 1) → ι) : tupIns k σ 0 = k := rfl

@[simp] lemma tupIns_succ (k : ι) {m : ℕ} (σ : Fin (m + 1) → ι) (b : Fin (m + 1)) :
    tupIns k σ b.succ = σ b := rfl

lemma tupRng_del_subset {m : ℕ} (i : Fin (m + 2)) (τ : Fin (m + 2) → ι) :
    tupRng (tupDel i τ) ⊆ tupRng τ := by
  intro x hx
  rw [tupRng, Finset.mem_image] at hx ⊢
  obtain ⟨b, -, hb⟩ := hx
  exact ⟨Fin.succAbove i b, Finset.mem_univ _, hb⟩

lemma tupRng_ins_subset (k : ι) {m : ℕ} (σ : Fin (m + 1) → ι) :
    tupRng σ ⊆ tupRng (tupIns k σ) := by
  intro x hx
  rw [tupRng, Finset.mem_image] at hx ⊢
  obtain ⟨b, -, hb⟩ := hx
  exact ⟨b.succ, Finset.mem_univ _, hb⟩

lemma tupDel_ins_zero (k : ι) {m : ℕ} (σ : Fin (m + 1) → ι) :
    tupDel (0 : Fin (m + 2)) (tupIns k σ) = σ := by
  funext b
  rw [tupDel_apply, Fin.succAbove_zero_apply, tupIns_succ]

lemma tupDel_ins_succ (k : ι) {m : ℕ} (σ : Fin (m + 2) → ι) (a : Fin (m + 2)) :
    tupDel a.succ (tupIns k σ) = tupIns k (tupDel a σ) := by
  funext b
  rw [tupDel_apply]
  cases b using Fin.cases with
  | zero =>
      have h : (Fin.succ (0 : Fin (m + 2)) : Fin (m + 3)) ≤ a.succ := by simp [Fin.le_def]
      rw [Fin.succAbove_of_succ_le _ _ h, Fin.castSucc_zero, tupIns_zero, tupIns_zero]
  | succ j =>
      rw [Fin.succ_succAbove_succ, tupIns_succ, tupIns_succ, tupDel_apply]

lemma tupRng_ins_del_subset (k : ι) {m : ℕ} (τ : Fin (m + 2) → ι) (i : Fin (m + 2)) :
    tupRng (tupIns k (tupDel i τ)) ⊆ tupRng (tupIns k τ) := by
  intro x hx
  rw [tupRng, Finset.mem_image] at hx ⊢
  obtain ⟨b, -, hb⟩ := hx
  cases b using Fin.cases with
  | zero => exact ⟨0, Finset.mem_univ _, by simpa using hb⟩
  | succ b =>
      refine ⟨(Fin.succAbove i b).succ, Finset.mem_univ _, ?_⟩
      rw [← hb]
      simp only [tupIns_succ, tupDel_apply]

lemma tupRng_nonempty {m : ℕ} (τ : Fin (m + 1) → ι) : (tupRng τ).Nonempty := by
  refine ⟨τ 0, ?_⟩
  rw [tupRng, Finset.mem_image]
  exact ⟨0, Finset.mem_univ _, rfl⟩

lemma tupRng_tupIns (k : ι) {m : ℕ} (τ : Fin (m + 1) → ι) :
    tupRng (tupIns k τ) = insert k (tupRng τ) := by
  ext x
  simp only [tupRng, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨b, rfl⟩
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨c, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨c, rfl⟩
  · rintro (rfl | ⟨c, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨c.succ, rfl⟩

end Defs

section Chart

variable (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R)

/-- The localisation map between perfected chart rings, restricted to the subalgebras. -/
noncomputable def rho {S T : Finset ι} (h : S ⊆ T) :
    perfChartRing p t S →ₐ[R] perfChartRing p t T where
  toFun x := ⟨locRes t h x.1, perfChartRing_map_le p t h ⟨x.1, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (locRes t h))
  map_mul' x y := Subtype.ext (map_mul (locRes t h) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (locRes t h))
  map_add' x y := Subtype.ext (map_add (locRes t h) x.1 y.1)
  commutes' r := Subtype.ext ((locRes t h).commutes r)

@[simp] lemma rho_coe {S T : Finset ι} (h : S ⊆ T) (x : perfChartRing p t S) :
    (rho p t h x : Localization.Away (tS t T)) = locRes t h x.1 := rfl

lemma rho_congr {S T : Finset ι} {h h' : S ⊆ T} (x : perfChartRing p t S) :
    rho p t h x = rho p t h' x := by
  apply Subtype.ext
  exact DFunLike.congr_fun (locRes_eq t h (locRes t h')) x.1

lemma rho_comp {S T V : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ V) (x : perfChartRing p t S) :
    rho p t h₂ (rho p t h₁ x) = rho p t (h₁.trans h₂) x := by
  apply Subtype.ext
  exact DFunLike.congr_fun
    (locRes_eq t (h₁.trans h₂) ((locRes t h₂).comp (locRes t h₁))) x.1

/-- The terms of the explicit perfected chart Čech complex. -/
noncomputable abbrev PCX (m : ℕ) : Type a := ∀ τ : Fin (m + 1) → ι, perfChartRing p t (tupRng τ)

/-- The alternating coface differential of the explicit complex, in coordinates. -/
noncomputable def PCd (m : ℕ) : PCX p t m →ₗ[R] PCX p t (m + 1) where
  toFun z := fun τ => ∑ i : Fin (m + 2),
    ((-1 : R) ^ ((i : ℕ))) • rho p t (tupRng_del_subset i τ) (z (tupDel i τ))
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul, smul_comm _ r, Finset.smul_sum]

@[simp] lemma PCd_apply (m : ℕ) (z : PCX p t m) (τ : Fin (m + 2) → ι) :
    PCd p t m z τ = ∑ i : Fin (m + 2),
      ((-1 : R) ^ ((i : ℕ))) • rho p t (tupRng_del_subset i τ) (z (tupDel i τ)) := rfl

/-- The *componentwise* `p`-th power map of the explicit complex (`ψ^{-1}`, the Frobenius).  It is
additive (characteristic `p`) and `R`-semilinear, but not `R`-linear. -/
noncomputable def phiPC (m : ℕ) (z : PCX p t m) : PCX p t m :=
  fun τ => ⟨(z τ).1 ^ p, (perfChartRing_pow_p_mem_iff p t (tupRng τ) _).2 (z τ).2⟩

@[simp] lemma phiPC_apply (m : ℕ) (z : PCX p t m) (τ : Fin (m + 1) → ι) :
    (phiPC p t m z τ : Localization.Away (tS t (tupRng τ))) = (z τ).1 ^ p := rfl

/-- **The staging of a cycle.**  Every element of the explicit perfected complex has, after raising
componentwise to the `p^e`-th power, all its components in the *honest* chart rings. -/
lemma phiPC_pow_mem_chartRing (m : ℕ) (z : PCX p t m) :
    ∃ e : ℕ, ∀ τ : Fin (m + 1) → ι, (z τ).1 ^ (p ^ e) ∈ chartRing t (tupRng τ) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have h : ∀ τ : Fin (m + 1) → ι, ∃ e : ℕ, (z τ).1 ^ (p ^ e) ∈ chartRing t (tupRng τ) :=
    fun τ => (mem_perfChartRing_iff p t (tupRng τ)).1 (z τ).2
  choose e he using h
  refine ⟨Finset.univ.sup e, fun τ => ?_⟩
  have hle : e τ ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ τ)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, pow_add, pow_mul]
  exact Subalgebra.pow_mem _ (he τ) _

end Chart

end Work.DSM5b
