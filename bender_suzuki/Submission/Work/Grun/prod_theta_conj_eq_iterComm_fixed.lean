/-
# Hall's cycle computation, in the form actually intended

`Work.Grun.prod_theta_conj_eq_iterComm` (file
`Submission/Work/Grun/prod_theta_conj_eq_iterComm.lean`) states the identity with the factor
written `w k⁻¹ * u * w k`.  Lean parses that as `w (k⁻¹) * u * w k`: `⁻¹` is postfix notation at
precedence `max`, so it binds tighter than application `w k`, and `ZMod p` has an `Inv` instance
because `[Fact p.Prime]` makes `ZMod p` a field.  The resulting statement is FALSE — a
counterexample is `G = D₈ = ⟨(1 2 3 4), (1 3)⟩ ≤ S₄`, `p = 2`, `H = ⟨(1 3)(2 4)⟩ ≅ C₂`,
`z = (1 3)`, `u = 1`, `w 0 = (1 2)(3 4)`, `w 1 = z * w 0 = (1 2 3 4)` (then `w k⁻¹ = w k` for
`k ∈ ZMod 2`, so the hypotheses hold while the left side is `θ((1 3)(2 4)) ≠ 1 =` the right
side).  With explicit parentheses the statement is the classical transfer computation of M. Hall,
*The Theory of Groups*, §14.4, pp. 210–211 (FT 1963, Lemma 17.2); it is proved here.

The proof is the standard one.  With `u_s := iterComm s u z` and `h_s k := (w k)⁻¹ * u_s * w k`:
since `w (k-1) = z⁻¹ * w k`, one has `h_{s+1} k = h_s k * (h_s (k-1))⁻¹`; applying `θ` and
inducting gives `θ (h_s k) = ∏_{j ≤ s} θ (h_0 (k-j)) ^ ((-1)^j * (s.choose j))`; for `s = p-1`
every exponent is `≡ 1 (mod p)` because `(p-1).choose j ≡ (-1)^j (mod p)`, and `A` has exponent
`p`; finally reindex `j ↦ -j`.
-/
import Mathlib
import Submission.Work.Grun.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise commutatorElement

namespace Work.Grun

variable {G : Type*} [Group G]
variable {p : ℕ} [Fact p.Prime]

/-! ### A product over `ZMod n` is a product over `range n` -/

/-- `ZMod n` is `Fin n` via `ZMod.val`. -/
def zmodEquivFin (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun x := ⟨x.val, ZMod.val_lt x⟩
  invFun i := (i : ZMod n)
  left_inv x := by
    show (((⟨x.val, ZMod.val_lt x⟩ : Fin n) : ℕ) : ZMod n) = x
    simp
  right_inv i := by
    apply Fin.ext
    simp [ZMod.val_natCast_of_lt i.2]

/-- Negation as a permutation of `ZMod n`. -/
def zmodNegEquiv (n : ℕ) : ZMod n ≃ ZMod n where
  toFun x := -x
  invFun x := -x
  left_inv x := by simp
  right_inv x := by simp

lemma zmod_prod_range {M : Type*} [CommMonoid M] (n : ℕ) [NeZero n] (f : ZMod n → M) :
    (∏ i : ZMod n, f i) = ∏ i ∈ Finset.range n, f (i : ZMod n) := by
  rw [Fintype.prod_equiv (zmodEquivFin n) f (fun i : Fin n => f (i : ZMod n))
    (by intro x; simp [zmodEquivFin])]
  exact Fin.prod_univ_eq_prod_range (fun i : ℕ => f (i : ZMod n)) n

/-! ### The recursion for the conjugates of the iterated commutators -/

/-- `w (k-1) = z⁻¹ * w k`, the step of the `z`-cycle read backwards. -/
lemma w_sub_one {z : G} {w : ZMod p → G} (hw : ∀ k : ZMod p, w (k+1) = z * w k) (k : ZMod p) :
    w k = z * w (k - 1) := by
  have h := hw (k - 1)
  rwa [sub_add_cancel] at h

/-- Hall's recursion: conjugating the iterated commutators by the `z`-cycle. -/
lemma conj_iterComm_rec {u z : G} {w : ZMod p → G} (hw : ∀ k : ZMod p, w (k+1) = z * w k)
    (s : ℕ) (k : ZMod p) :
    (w k)⁻¹ * iterComm (s+1) u z * w k =
      ((w k)⁻¹ * iterComm s u z * w k) * ((w (k-1))⁻¹ * iterComm s u z * w (k-1))⁻¹ := by
  rw [w_sub_one hw k, iterComm_succ, commutatorElement_def]
  group

/-! ### The `H`-valued cycle elements and their images in `A` -/

section Main

variable {H : Subgroup G} {u : G} {w : ZMod p → G} {z : G}

/-- `h_s k = (w k)⁻¹ * iterComm s u z * w k`, an element of `H` whenever `s = 0` satisfies the
membership hypothesis; defined by Hall's recursion. -/
noncomputable def hIter (hmem : ∀ k : ZMod p, (w k)⁻¹ * u * w k ∈ H) : ℕ → ZMod p → H
  | 0, k => ⟨(w k)⁻¹ * u * w k, hmem k⟩
  | s+1, k => hIter hmem s k * (hIter hmem s (k-1))⁻¹

lemma hIter_succ (hmem : ∀ k : ZMod p, (w k)⁻¹ * u * w k ∈ H) (s : ℕ) (k : ZMod p) :
    hIter hmem (s+1) k = hIter hmem s k * (hIter hmem s (k-1))⁻¹ := rfl

lemma hIter_coe (hw : ∀ k : ZMod p, w (k+1) = z * w k)
    (hmem : ∀ k : ZMod p, (w k)⁻¹ * u * w k ∈ H) :
    ∀ (s : ℕ) (k : ZMod p), ((hIter hmem s k : H) : G) = (w k)⁻¹ * iterComm s u z * w k
  | 0, k => rfl
  | s+1, k => by
      rw [hIter_succ, Subgroup.coe_mul, Subgroup.coe_inv, hIter_coe hw hmem s k,
        hIter_coe hw hmem s (k-1)]
      exact (conj_iterComm_rec hw s k).symm

variable {A : Type*} [CommGroup A]

/-- `θ (h_s k) ∈ A`. -/
noncomputable def conjIter (hmem : ∀ k : ZMod p, (w k)⁻¹ * u * w k ∈ H) (θ : H →* A)
    (s : ℕ) (k : ZMod p) : A := θ (hIter hmem s k)

lemma conjIter_succ (hmem : ∀ k : ZMod p, (w k)⁻¹ * u * w k ∈ H) (θ : H →* A)
    (s : ℕ) (k : ZMod p) :
    conjIter hmem θ (s+1) k = conjIter hmem θ s k * (conjIter hmem θ s (k-1))⁻¹ := by
  simp only [conjIter, hIter_succ, map_mul, map_inv]

/-! ### The explicit binomial formula -/

/-- The exponent `(-1)^j * (s.choose j)`. -/
def binomExp (s j : ℕ) : ℤ := (-1 : ℤ) ^ j * ((s.choose j : ℤ))

@[simp] lemma binomExp_zero_right (s : ℕ) : binomExp s 0 = 1 := by simp [binomExp]

lemma binomExp_succ_succ (s i : ℕ) : binomExp (s+1) (i+1) = binomExp s (i+1) - binomExp s i := by
  have hp : (-1 : ℤ) ^ (i + 1) = -(-1) ^ i := by rw [pow_succ]; ring
  simp only [binomExp, Nat.choose_succ_succ, Nat.cast_add, hp]
  ring

lemma binomExp_eq_zero_of_lt (s j : ℕ) (h : s < j) : binomExp s j = 0 := by
  simp [binomExp, Nat.choose_eq_zero_of_lt h]

/-- Pure product identity: the Lagrange/binomial recursion for the exponents `(-1)^j * (s.choose j)`. -/
lemma prod_rec (c : ZMod p → A) (s : ℕ) (k : ZMod p) :
    (∏ j ∈ Finset.range (s+2), c (k - (j : ZMod p)) ^ binomExp (s+1) j)
      = (∏ j ∈ Finset.range (s+1), c (k - (j : ZMod p)) ^ binomExp s j)
        * (∏ j ∈ Finset.range (s+1), c ((k-1) - (j : ZMod p)) ^ binomExp s j)⁻¹ := by
  have base : ∀ j : ℕ, k - ((j:ℕ) : ZMod p) - 1 = k - (↑(j+1) : ZMod p) := by
    intro j; push_cast; ring
  have key : ∀ j : ℕ, c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp (s+1) (j+1)
        = c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s (j+1)
          * (c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s j)⁻¹ := by
    intro j
    have h : binomExp (s+1) (j+1) = binomExp s (j+1) + (-(binomExp s j)) := by
      rw [binomExp_succ_succ]; ring
    rw [h, zpow_add, zpow_neg]
  have hL : (∏ j ∈ Finset.range (s+2), c (k - (j : ZMod p)) ^ binomExp (s+1) j)
      = (∏ j ∈ Finset.range (s+1), c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp (s+1) (j+1)) * c k := by
    rw [show s+2 = (s+1)+1 by ring, Finset.prod_range_succ',
      Finset.prod_congr rfl (fun j _ => by rw [← base j])]
    simp [binomExp]
  have hkey : (∏ j ∈ Finset.range (s+1), c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp (s+1) (j+1))
      = (∏ j ∈ Finset.range (s+1), c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s (j+1))
        * (∏ j ∈ Finset.range (s+1), c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s j)⁻¹ := by
    rw [Finset.prod_congr rfl (fun j _ => key j), Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hA : (∏ j ∈ Finset.range (s+1), c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s (j+1))
      = ∏ j ∈ Finset.range s, c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s (j+1) := by
    rw [Finset.prod_range_succ, binomExp_eq_zero_of_lt s (s+1) (Nat.lt_succ_self s), zpow_zero,
      mul_one]
  have hB : (∏ j ∈ Finset.range (s+1), c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s j)
      = ∏ j ∈ Finset.range (s+1), c ((k-1) - ((j:ℕ) : ZMod p)) ^ binomExp s j := by
    apply Finset.prod_congr rfl
    intro j _
    congr 2
    ring
  have hC : (∏ j ∈ Finset.range (s+1), c (k - (j : ZMod p)) ^ binomExp s j)
      = c k * ∏ j ∈ Finset.range s, c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s (j+1) := by
    rw [Finset.prod_range_succ']
    rw [Finset.prod_congr rfl (fun j _ => by rw [← base j])]
    rw [show c (k - ((0:ℕ):ZMod p)) ^ binomExp s 0 = c k by simp]
    exact mul_comm _ _
  calc (∏ j ∈ Finset.range (s+2), c (k - (j : ZMod p)) ^ binomExp (s+1) j)
      = (∏ j ∈ Finset.range (s+1), c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp (s+1) (j+1))
          * c k := hL
    _ = ((∏ j ∈ Finset.range (s+1), c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s (j+1))
          * (∏ j ∈ Finset.range (s+1), c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s j)⁻¹) * c k := by
        rw [hkey]
    _ = ((∏ j ∈ Finset.range s, c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s (j+1))
          * (∏ j ∈ Finset.range (s+1), c ((k-1) - ((j:ℕ) : ZMod p)) ^ binomExp s j)⁻¹) * c k := by
        rw [hA, hB]
    _ = (c k * ∏ j ∈ Finset.range s, c (k - ((j:ℕ):ZMod p) - 1) ^ binomExp s (j+1))
          * (∏ j ∈ Finset.range (s+1), c ((k-1) - ((j:ℕ) : ZMod p)) ^ binomExp s j)⁻¹ := by
        ac_rfl
    _ = (∏ j ∈ Finset.range (s+1), c (k - (j : ZMod p)) ^ binomExp s j)
          * (∏ j ∈ Finset.range (s+1), c ((k-1) - (j : ZMod p)) ^ binomExp s j)⁻¹ := by
        rw [hC]

/-- The right-hand side of the formula at level `s`. -/
noncomputable def prodP (hmem : ∀ k : ZMod p, (w k)⁻¹ * u * w k ∈ H) (θ : H →* A)
    (s : ℕ) (k : ZMod p) : A :=
  ∏ j ∈ Finset.range (s+1), conjIter hmem θ 0 (k - (j : ZMod p)) ^ binomExp s j

lemma prodP_succ (hmem : ∀ k : ZMod p, (w k)⁻¹ * u * w k ∈ H) (θ : H →* A)
    (s : ℕ) (k : ZMod p) :
    prodP hmem θ (s+1) k = prodP hmem θ s k * (prodP hmem θ s (k-1))⁻¹ :=
  prod_rec (fun m => conjIter hmem θ 0 m) s k

/-- The binomial formula for the conjugates of the iterated commutators. -/
lemma conjIter_eq_prodP (hmem : ∀ k : ZMod p, (w k)⁻¹ * u * w k ∈ H) (θ : H →* A)
    (s : ℕ) (k : ZMod p) : conjIter hmem θ s k = prodP hmem θ s k := by
  induction s generalizing k with
  | zero =>
      rw [prodP, Finset.prod_range_succ']
      simp [conjIter, binomExp]
  | succ n ih =>
      rw [conjIter_succ, ih k, ih (k-1), prodP_succ]

/-! ### The binomial congruence `(p-1).choose j ≡ (-1)^j (mod p)` -/

lemma zmod_choose_p_sub_one (j : ℕ) (hj : j ≤ p - 1) :
    (((p - 1).choose j : ℕ) : ZMod p) = (-1 : ZMod p) ^ j := by
  have hs : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  induction j with
  | zero => simp
  | succ i ih =>
      have hi : i ≤ p - 1 := Nat.le_of_succ_le hj
      have hlt : i + 1 < p := by omega
      have hpas : p.choose (i + 1) = (p - 1).choose i + (p - 1).choose (i + 1) := by
        rw [← hs]
        exact Nat.choose_succ_succ' (p - 1) i
      have hzero : ((p.choose (i + 1) : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact (Fact.out : p.Prime).dvd_choose_self (by omega) hlt
      have hcast : (((p - 1).choose i : ℕ) : ZMod p)
          + (((p - 1).choose (i + 1) : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, ← hpas]
        exact hzero
      have hneg : (((p - 1).choose (i + 1) : ℕ) : ZMod p)
          = -(((p - 1).choose i : ℕ) : ZMod p) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hcast
      rw [hneg, ih hi, pow_succ]
      ring

/-- The exponents `(-1)^j * (p-1).choose j` are all `≡ 1 (mod p)`. -/
lemma binomExp_modEq_one (j : ℕ) (hj : j ≤ p - 1) : binomExp (p - 1) j ≡ 1 [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  simp only [binomExp]
  push_cast
  rw [zmod_choose_p_sub_one j hj, ← mul_pow]
  simp

/-- In a group of exponent `p`, `a ^ m = a` whenever `m ≡ 1 (mod p)`. -/
lemma zpow_eq_self_of_modEq {n : ℕ} (hexp : ∀ a : A, a ^ n = 1) {m : ℤ}
    (hm : m ≡ 1 [ZMOD n]) (a : A) : a ^ m = a := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 1 - m = (n : ℤ) * k := hm.dvd
  have hm' : m = 1 + (-((n : ℤ) * k)) := by linarith
  rw [hm', zpow_add, zpow_one, zpow_neg, zpow_mul, zpow_natCast, hexp a]
  simp

end Main

/-! ### Hall's cycle computation -/

/-- Hall's cycle computation (M. Hall, §14.4, pp. 210–211): for the representatives `w` of a
`z`-cycle of cosets of `H` fixed by `u`, `∏ k, θ (w k⁻¹ * u * w k) = θ (w 0⁻¹ * e_p(u,z) * w 0)`
with `e_p(u,z) = iterComm (p-1) u z`.  (All inverse signs in this statement are parenthesised:
`(w k)⁻¹`, not `w (k⁻¹)`.) -/
theorem prod_theta_conj_eq_iterComm_fixed {G : Type*} [Group G] {H : Subgroup G} {p : ℕ}
    [Fact p.Prime] {A : Type*} [CommGroup A] (θ : H →* A) (hexp : ∀ a : A, a ^ p = 1)
    (u z : G) (w : ZMod p → G)
    (hw : ∀ k : ZMod p, w (k + 1) = z * w k)
    (hmem : ∀ k : ZMod p, (w k)⁻¹ * u * w k ∈ H)
    (hmem0 : (w 0)⁻¹ * Work.Grun.iterComm (p - 1) u z * w 0 ∈ H) :
    (∏ k : ZMod p, θ ⟨(w k)⁻¹ * u * w k, hmem k⟩) =
      θ ⟨(w 0)⁻¹ * Work.Grun.iterComm (p - 1) u z * w 0, hmem0⟩ := by
  have hs : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hRHS : conjIter hmem θ (p - 1) 0
      = θ ⟨(w 0)⁻¹ * Work.Grun.iterComm (p - 1) u z * w 0, hmem0⟩ := by
    simp only [conjIter]
    congr 1
    exact Subtype.ext (hIter_coe hw hmem (p - 1) 0)
  have hLHS : (∏ k : ZMod p, θ ⟨(w k)⁻¹ * u * w k, hmem k⟩)
      = ∏ k : ZMod p, conjIter hmem θ 0 k :=
    Finset.prod_congr rfl fun k _ => rfl
  rw [hLHS, ← hRHS, conjIter_eq_prodP, prodP, hs]
  calc (∏ k : ZMod p, conjIter hmem θ 0 k)
      = ∏ k : ZMod p, conjIter hmem θ 0 (0 - k) := by
        refine Fintype.prod_equiv (zmodNegEquiv p) (fun k => conjIter hmem θ 0 k)
          (fun k => conjIter hmem θ 0 (0 - k)) ?_
        intro k
        simp [zmodNegEquiv]
    _ = ∏ j ∈ Finset.range p, conjIter hmem θ 0 (0 - (j : ZMod p)) :=
        zmod_prod_range p (fun k => conjIter hmem θ 0 (0 - k))
    _ = ∏ j ∈ Finset.range p, conjIter hmem θ 0 (0 - (j : ZMod p)) ^ binomExp (p - 1) j := by
        refine Finset.prod_congr rfl fun j hj => ?_
        exact (zpow_eq_self_of_modEq hexp
          (binomExp_modEq_one j (Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)))
          (conjIter hmem θ 0 (0 - (j : ZMod p)))).symm

end Work.Grun
