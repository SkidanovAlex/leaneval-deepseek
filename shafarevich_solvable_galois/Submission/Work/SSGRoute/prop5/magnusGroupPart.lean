import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
import Submission.Work.SSGRoute.prop5.magnusLieDefs
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus leading-term map on the lower central series

For the free group `F = FreeGroup X` and the truncation `N` we let
`R_N = FreeAssoc X ⧸ fil X N` and

`magLead N z = (magnus X N z : R_N) - 1`.

For `z ∈ γ_k` (Mathlib: `(⊤ : Subgroup F).lowerCentralSeries (k-1)`) and `N ≥ k` this lies in the
degree-`k` part `filq X N k`, it is additive on `γ_k` (modulo `filq X N (k+1)`), it converts
`p`-th powers into multiplication by `p`, and it converts commutators into ring commutators:
for `u ∈ γ_p`, `v ∈ γ_q` one has
`magLead N ⁅u,v⁆ - [magLead N u, magLead N v] ∈ filq X N (p+q+1)`
where `[a,b] = a*b - b*a` is the ring commutator.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-- The Magnus leading term of `z` at truncation `N`: the Magnus image modulo `fil X N`, shifted
by `1`. -/
def magLead (N : ℕ) (z : FreeGroup X) : FreeAssoc X ⧸ fil X N :=
  ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1

@[simp]
theorem magLead_one (N : ℕ) : magLead (X := X) N 1 = 0 := by
  simp [magLead]

/-- The leading term of a generator. -/
theorem magLead_of (N : ℕ) (x : X) :
    magLead N (FreeGroup.of x) = Ideal.Quotient.mk (fil X N) (wordEl [x]) := by
  rw [magLead, magnus_of]
  have : (MonoidAlgebra.single (FreeMonoid.of x) (1 : ℤ)) = wordEl [x] := by simp [wordEl]
  rw [this]
  noncomm_ring

/-- The `N`-th filtration piece of the truncated algebra is zero. -/
theorem filq_self_eq_bot' (N : ℕ) : filq X N N = ⊥ := by
  rw [filq, Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  rw [RingHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

theorem mem_filq_self_eq_zero' {N : ℕ} {x : FreeAssoc X ⧸ fil X N} (h : x ∈ filq X N N) :
    x = 0 := by
  rw [filq_self_eq_bot'] at h
  exact h

/-- The "easy half" of the Magnus embedding: the leading term of an element of `γ_k` (Mathlib
indexing: `lowerCentralSeries (k-1)`) lies in the degree-`k` part. -/
theorem magLead_mem_filq (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    magLead N z ∈ filq X N k := by
  have h := magnus_mem_one_add X N (k - 1) (by omega) z hz
  rwa [Nat.sub_add_cancel hk] at h

/-- The leading term vanishes on `γ_{k+1}`. -/
theorem magLead_eq_zero_of_mem_succ (k : ℕ) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k) :
    magLead (k + 1) z = 0 := by
  have h1 : magLead (k + 1) z ∈ filq X (k + 1) (k + 1) :=
    magLead_mem_filq (k + 1) (k + 1) (by omega) le_rfl (by simpa using hz)
  exact mem_filq_self_eq_zero' h1

/-- **Additivity of the leading term on `γ_k`** (when `2k ≥ N`). -/
theorem magLead_mul (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hN2 : N ≤ 2 * k) {g h : FreeGroup X}
    (hg : g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1))
    (hh : h ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    magLead N (g * h) = magLead N g + magLead N h := by
  have hsq : magLead N g * magLead N h = 0 := by
    refine mem_filq_self_eq_zero' ?_
    refine (filq_antitone X N (by omega : N ≤ k + k)) ?_
    exact mul_mem_filq X N k k (magLead_mem_filq N k hk hkN hg) (magLead_mem_filq N k hk hkN hh)
  have key : magLead N (g * h) = magLead N g + magLead N h + magLead N g * magLead N h := by
    unfold magLead
    rw [map_mul, Units.val_mul]
    noncomm_ring
  rw [key, hsq, add_zero]

/-- The leading term of an inverse. -/
theorem magLead_inv (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hN2 : N ≤ 2 * k) {w : FreeGroup X}
    (hw : w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    magLead N w⁻¹ = -magLead N w := by
  have h1 : magLead N (w * w⁻¹) = 0 := by rw [mul_inv_cancel]; exact magLead_one N
  have h2 := magLead_mul N k hk hkN hN2 hw (Subgroup.inv_mem _ hw)
  rw [h1] at h2
  have h3 : magLead N w⁻¹ + magLead N w = 0 := by
    rw [add_comm (magLead N w⁻¹) (magLead N w)]; exact h2.symm
  exact eq_neg_of_add_eq_zero_left h3

/-- The leading term of a `p`-th power is `p` times the leading term (for `w ∈ γ_k`). -/
theorem magLead_pow (N k p : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hN2 : N ≤ 2 * k) {w : FreeGroup X}
    (hw : w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    magLead N (w ^ p) = (p : ℤ) * magLead N w := by
  have hsq : magLead N w * magLead N w = 0 := by
    refine mem_filq_self_eq_zero' ?_
    refine (filq_antitone X N (by omega : N ≤ k + k)) ?_
    exact mul_mem_filq X N k k (magLead_mem_filq N k hk hkN hw) (magLead_mem_filq N k hk hkN hw)
  have key : magLead N (w ^ p) = (1 + magLead N w) ^ p - 1 := by
    unfold magLead
    rw [map_pow, Units.val_pow_eq_pow_val]
    rw [show (1 : FreeAssoc X ⧸ fil X N) +
        (((magnus X N w : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1)
        = ((magnus X N w : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
        from by noncomm_ring]
  rw [key, one_add_pow_eq_of_sq_zero (magLead N w) hsq p, add_sub_cancel_left]
  exact nsmul_eq_mul p (magLead N w)

/-! ## The commutator identity -/

/-- The pure unit-group identity behind the bracket lemma: for units `A`, `B` of a ring,
`A B A⁻¹ B⁻¹ - 1 = ((A-1)(B-1) - (B-1)(A-1)) * (A⁻¹ B⁻¹)`. -/
theorem commutator_sub_one {R : Type*} [Ring R] (A B : Rˣ) :
    ((⁅A, B⁆ : Rˣ) : R) - 1
      = ((((A : R) - 1) * ((B : R) - 1) - ((B : R) - 1) * ((A : R) - 1))
          * (((A⁻¹ : Rˣ) : R) * ((B⁻¹ : Rˣ) : R))) := by
  have key : (A : R) * (B : R) - (B : R) * (A : R)
      = ((A : R) - 1) * ((B : R) - 1) - ((B : R) - 1) * ((A : R) - 1) := by noncomm_ring
  rw [← key, commutatorElement_def, sub_mul]
  simp only [Units.val_mul]
  have h3 : ((B : R) * (A : R)) * (((A⁻¹ : Rˣ) : R) * ((B⁻¹ : Rˣ) : R)) = 1 := by
    have hgrp : (B * A * (A⁻¹ * B⁻¹) : Rˣ) = 1 := by group
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hgrp, Units.val_one]
  rw [h3]
  simp only [mul_assoc]



/-! ## The bracket lemma -/

/-- The inverse of a Magnus image is congruent to `1` modulo the first filtration piece. -/
theorem magnus_inv_sub_one_mem (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    (((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 ∈ filq X N 1 := by
  have hz' : magLead N z ∈ filq X N k := magLead_mem_filq N k hk hkN hz
  have h1 : (((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
      * ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h : (((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      = - ((((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
          * (((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1)) := by
    rw [mul_sub, mul_one, h1, neg_sub]
  rw [h]
  refine neg_mem ?_
  rw [show ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      = magLead N z from rfl]
  exact Ideal.mul_mem_left _ _ ((filq_antitone X N hk) hz')

/-- **The bracket lemma**: for `u ∈ γ_p` and `v ∈ γ_q` the leading term of `⁅u,v⁆` agrees modulo
`filq X N (p+q+1)` with the ring commutator of the leading terms. -/
theorem magLead_commutator (N p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p + q + 1 ≤ N)
    {u v : FreeGroup X}
    (hu : u ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (p - 1))
    (hv : v ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (q - 1)) :
    magLead N ⁅u,v⁆ - (magLead N u * magLead N v - magLead N v * magLead N u) ∈
      filq X N (p + q + 1) := by
  have hpu : p ≤ N := by omega
  have hqv : q ≤ N := by omega
  have hmemu : magLead N u ∈ filq X N p := magLead_mem_filq N p hp hpu hu
  have hmemv : magLead N v ∈ filq X N q := magLead_mem_filq N q hq hqv hv
  have hinvu : (((magnus X N u)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      ∈ filq X N 1 := magnus_inv_sub_one_mem N p hp hpu hu
  have hinvv : (((magnus X N v)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      ∈ filq X N 1 := magnus_inv_sub_one_mem N q hq hqv hv
  set A : (FreeAssoc X ⧸ fil X N)ˣ := magnus X N u with hA
  set B : (FreeAssoc X ⧸ fil X N)ˣ := magnus X N v with hB
  have hAu : ((A : FreeAssoc X ⧸ fil X N)) - 1 = magLead N u := rfl
  have hBv : ((B : FreeAssoc X ⧸ fil X N)) - 1 = magLead N v := rfl
  have hmap : magnus X N ⁅u,v⁆ = ⁅A, B⁆ := by
    rw [hA, hB, map_commutatorElement]
  have hlt : magLead N ⁅u,v⁆
      = ((((A : FreeAssoc X ⧸ fil X N)) - 1) * (((B : FreeAssoc X ⧸ fil X N)) - 1)
          - (((B : FreeAssoc X ⧸ fil X N)) - 1) * (((A : FreeAssoc X ⧸ fil X N)) - 1))
        * ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
            * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) := by
    rw [magLead, hmap, commutator_sub_one]
  -- the difference is `X * (A⁻¹B⁻¹ - 1)` with `X ∈ filq N (p+q)` and `A⁻¹B⁻¹ - 1 ∈ filq N 1`
  have hY : ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
        * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) - 1
      ∈ filq X N 1 := by
    have h2 : ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
          * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) - 1
        = ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)) - 1)
            * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
          + ((((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)) - 1) := by
      noncomm_ring
    rw [h2]
    exact Submodule.add_mem _ (Ideal.mul_mem_right _ _ (by rw [hA]; exact hinvu)) (by rw [hB]; exact hinvv)
  have hX : (((A : FreeAssoc X ⧸ fil X N)) - 1) * (((B : FreeAssoc X ⧸ fil X N)) - 1)
      - (((B : FreeAssoc X ⧸ fil X N)) - 1) * (((A : FreeAssoc X ⧸ fil X N)) - 1)
      ∈ filq X N (p + q) := by
    rw [hAu, hBv]
    refine Submodule.sub_mem _ (mul_mem_filq X N p q hmemu hmemv) ?_
    exact (Nat.add_comm p q) ▸ mul_mem_filq X N q p hmemv hmemu
  have hkey : magLead N ⁅u,v⁆ - (magLead N u * magLead N v - magLead N v * magLead N u)
      = ((((A : FreeAssoc X ⧸ fil X N)) - 1) * (((B : FreeAssoc X ⧸ fil X N)) - 1)
          - (((B : FreeAssoc X ⧸ fil X N)) - 1) * (((A : FreeAssoc X ⧸ fil X N)) - 1))
        * (((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
            * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) - 1) := by
    rw [hlt, hAu, hBv]
    noncomm_ring
  rw [hkey]
  exact mul_mem_filq X N (p + q) 1 hX hY



/-! ## The realization of the left-nested span by group commutators -/

/-- The left-nested group commutator attached to a word: `[x₁,[x₂,…]]` in the group. -/
def lc : List X → FreeGroup X
  | [] => 1
  | x :: rest => rest.foldl (fun acc y => ⁅acc, FreeGroup.of y⁆) (FreeGroup.of x)

/-- The algebra fold: `A₀ ↦ [[A₀, x], y] …`. -/
def alFold (A₀ : FreeAssoc X) (vs : List X) : FreeAssoc X :=
  vs.foldl (fun acc y => acc * wordEl [y] - wordEl [y] * acc) A₀

/-- The group fold: `u ↦ [[u, x], y] …`. -/
def gpFold (u : FreeGroup X) (vs : List X) : FreeGroup X :=
  vs.foldl (fun acc y => ⁅acc, FreeGroup.of y⁆) u

theorem lnMon_eq_alFold (x : X) (rest : List X) : lnMon (x :: rest) = alFold (wordEl [x]) rest := rfl

theorem lc_eq_gpFold (x : X) (rest : List X) : lc (x :: rest) = gpFold (FreeGroup.of x) rest := rfl

theorem gpFold_mem (vs : List X) (p : ℕ) (hp : 1 ≤ p) {u : FreeGroup X}
    (hu : u ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (p - 1)) :
    gpFold u vs ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (p + vs.length - 1) := by
  induction vs generalizing u p with
  | nil => simpa [gpFold, List.foldl_nil, List.length_nil, Nat.add_zero] using hu
  | cons y vs ih =>
      rw [gpFold, List.foldl_cons]
      have hcomm : ⁅u, FreeGroup.of y⁆ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries ((p + 1) - 1) := by
        have := commutator_lowerCentralSeries_le (FreeGroup X) (p - 1) 0
          (Subgroup.commutator_mem_commutator hu (Subgroup.mem_top (FreeGroup.of y)))
        simpa [Nat.sub_add_cancel hp, Nat.add_zero] using this
      have := ih (p + 1) (by omega) hcomm
      rw [gpFold] at this
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this


/-- **The congruence step of the fold.** -/
theorem alFold_gpFold_congr (N : ℕ) (vs : List X) (p : ℕ) (hp : 1 ≤ p)
    (hN : p + vs.length + 1 ≤ N) {u : FreeGroup X} {A₀ : FreeAssoc X}
    (hu : u ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (p - 1))
    (hA : (Ideal.Quotient.mk (fil X N) A₀) - magLead N u ∈ filq X N (p + 1)) :
    (Ideal.Quotient.mk (fil X N) (alFold A₀ vs)) - magLead N (gpFold u vs) ∈
      filq X N (p + vs.length + 1) := by
  induction vs generalizing u A₀ p with
  | nil => simpa [alFold, gpFold, List.foldl_nil, List.length_nil, Nat.add_zero] using hA
  | cons y vs ih =>
      rw [alFold, gpFold, List.foldl_cons, List.foldl_cons]
      have hu'mem : ⁅u, FreeGroup.of y⁆ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries ((p + 1) - 1) := by
        have h := commutator_lowerCentralSeries_le (FreeGroup X) (p - 1) 0
          (Subgroup.commutator_mem_commutator hu (Subgroup.mem_top (FreeGroup.of y)))
        have hidx : (p - 1) + 0 + 1 = p := by omega
        rw [hidx] at h
        simpa [Nat.add_sub_cancel] using h
      have hxmem : (Ideal.Quotient.mk (fil X N) (wordEl [y])) ∈ filq X N 1 := by
        have h1 := magLead_mem_filq N 1 le_rfl (by omega : 1 ≤ N) (z := FreeGroup.of y)
          (Subgroup.mem_top _)
        rwa [magLead_of] at h1
      have hnew : (Ideal.Quotient.mk (fil X N) (A₀ * wordEl [y] - wordEl [y] * A₀))
          - magLead N ⁅u, FreeGroup.of y⁆ ∈ filq X N ((p + 1) + 1) := by
        have hlenv : (y :: vs).length = vs.length + 1 := by simp
        have hpq : p + 1 + 1 ≤ N := by omega
        have hv0 : (FreeGroup.of y) ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (1 - 1) := by
          rw [Subgroup.lowerCentralSeries_zero]; exact Subgroup.mem_top _
        have hb := magLead_commutator N p 1 hp le_rfl hpq hu hv0
        rw [magLead_of] at hb
        rw [map_sub, map_mul, map_mul]
        have hD1 : (Ideal.Quotient.mk (fil X N) A₀ * Ideal.Quotient.mk (fil X N) (wordEl [y])
              - Ideal.Quotient.mk (fil X N) (wordEl [y]) * Ideal.Quotient.mk (fil X N) A₀)
            - (magLead N u * Ideal.Quotient.mk (fil X N) (wordEl [y])
              - Ideal.Quotient.mk (fil X N) (wordEl [y]) * magLead N u) ∈ filq X N (p + 1 + 1) := by
          have h1 : (Ideal.Quotient.mk (fil X N) A₀ * Ideal.Quotient.mk (fil X N) (wordEl [y])
                - Ideal.Quotient.mk (fil X N) (wordEl [y]) * Ideal.Quotient.mk (fil X N) A₀)
              - (magLead N u * Ideal.Quotient.mk (fil X N) (wordEl [y])
                - Ideal.Quotient.mk (fil X N) (wordEl [y]) * magLead N u)
              = ((Ideal.Quotient.mk (fil X N) A₀) - magLead N u)
                  * Ideal.Quotient.mk (fil X N) (wordEl [y])
                - Ideal.Quotient.mk (fil X N) (wordEl [y])
                  * ((Ideal.Quotient.mk (fil X N) A₀) - magLead N u) := by
            noncomm_ring
          rw [h1]
          refine Submodule.sub_mem _ (mul_mem_filq X N (p + 1) 1 hA hxmem) ?_
          have h2 := mul_mem_filq X N 1 (p + 1) hxmem hA
          have heq2 : 1 + (p + 1) = p + 1 + 1 := by omega
          rwa [heq2] at h2
        have hD2 : magLead N ⁅u, FreeGroup.of y⁆
            - (magLead N u * Ideal.Quotient.mk (fil X N) (wordEl [y])
              - Ideal.Quotient.mk (fil X N) (wordEl [y]) * magLead N u) ∈ filq X N (p + 1 + 1) := hb
        have hsum := Submodule.sub_mem _ hD1 hD2
        have heq : ((Ideal.Quotient.mk (fil X N) A₀ * Ideal.Quotient.mk (fil X N) (wordEl [y])
              - Ideal.Quotient.mk (fil X N) (wordEl [y]) * Ideal.Quotient.mk (fil X N) A₀)
            - (magLead N u * Ideal.Quotient.mk (fil X N) (wordEl [y])
              - Ideal.Quotient.mk (fil X N) (wordEl [y]) * magLead N u))
            - (magLead N ⁅u, FreeGroup.of y⁆
              - (magLead N u * Ideal.Quotient.mk (fil X N) (wordEl [y])
                - Ideal.Quotient.mk (fil X N) (wordEl [y]) * magLead N u))
            = Ideal.Quotient.mk (fil X N) A₀ * Ideal.Quotient.mk (fil X N) (wordEl [y])
              - Ideal.Quotient.mk (fil X N) (wordEl [y]) * Ideal.Quotient.mk (fil X N) A₀
              - magLead N ⁅u, FreeGroup.of y⁆ := by noncomm_ring
        rwa [heq] at hsum
      have hbnd : (p + 1) + vs.length + 1 ≤ N := by
        have := hN
        simp only [List.length_cons] at this
        omega
      have hih := ih (p + 1) (by omega) hbnd hu'mem hnew
      have hidx2 : (p + 1) + vs.length + 1 = p + (y :: vs).length + 1 := by
        simp only [List.length_cons]; omega
      rw [hidx2] at hih
      simpa only [alFold, gpFold] using hih

/-- **Realization**: for a word `w` of length `j` and `N ≥ j+1`, the left-nested group
commutator `lc w` lies in `γ_j` and its Magnus leading term is congruent to `lnMon w` modulo
`filq X N (j+1)`. -/
theorem magLead_lc_congr (N : ℕ) {w : List X} (hw : 1 ≤ w.length) (hN : w.length + 1 ≤ N) :
    magLead N (lc w) - (Ideal.Quotient.mk (fil X N)) (lnMon w) ∈ filq X N (w.length + 1) := by
  cases w with
  | nil => simp at hw
  | cons x rest =>
      have hbase : (Ideal.Quotient.mk (fil X N) (wordEl [x])) - magLead N (FreeGroup.of x)
          ∈ filq X N (1 + 1) := by
        rw [magLead_of, sub_self]
        exact Submodule.zero_mem _
      have hbound : 1 + rest.length + 1 ≤ N := by
        simp only [List.length_cons] at hN
        omega
      have h := alFold_gpFold_congr N rest 1 le_rfl hbound (u := FreeGroup.of x)
        (Subgroup.mem_top _) (A₀ := wordEl [x]) hbase
      rw [lnMon_eq_alFold, lc_eq_gpFold]
      have hlen : 1 + rest.length + 1 = (x :: rest).length + 1 := by
        simp only [List.length_cons]; omega
      rw [hlen] at h
      simpa only [neg_sub] using neg_mem h

end Work.SSGRoute.prop5
