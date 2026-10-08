import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV3.Prove.conj_mem_W_of_mem_centD
import Submission.Work.ThmF.ChV3.Prove.commutator_mem_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.commV_mem_W` — `V/W` is abelian (Peterfalvi II Ch. V §3)

`V = C_D(t) = centD H t`, `W = C_V(K) = W H t` and `K = J(D,t) = Kset H t`.  Step (1) of §3
(`Chain15.hV`) gives `V = W ⋊ P` with `P ≤ V` of prime order.  Hence `V/W ≅ P`-modulo its
intersection with `W`, which is trivial (`Chain15.hWP`), so `V/W` is a quotient of the *cyclic*
group `P` — in particular abelian — and every commutator of two elements of `V` lies in `W`.

Two reusable ingredients:

* `conj_mem_W_of_mem_centD` — `W` is normalised by `V` (so `W ⊴ V`, `V ≤ N_G(W)`);
* `commutator_mem_of_le_normalizer` — the abstract group-theoretic statement: if `P ≤ N_G(W)`
  and `P` is commutative, then every commutator of two elements of `W ⊔ P` lies in `W`.

The assembly is then: `V = W ⊔ P` (`h15.hV`), `P ≤ N_G(W)` (first ingredient applied to
`P ≤ V`), and `P` commutative because `|P|` is prime (a group of prime order is cyclic).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ThmF.ChV3.Prove

/-- `P ≤ V = W ⋊ P`: the second factor of step (1) of §3. -/
private theorem P_le_centD {G : Type} [Group G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) :
    P ≤ Submission.Blueprint.centD H t :=
  fun _ hp => h15.hV ▸ Subgroup.mem_sup_right hp

/-- `V ≤ N_G(W)`: `W = C_V(K)` is normal in `V = C_D(t)`. -/
private theorem centD_le_normalizer_W {G : Type} [Group G] {H : Subgroup G} {t : G} :
    Submission.Blueprint.centD H t ≤ Subgroup.normalizer (Work.ThmF.W H t : Set G) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact conj_mem_W_of_mem_centD hv hw
  · intro hw
    have h1 : v⁻¹ * (v * w * v⁻¹) * (v⁻¹)⁻¹ ∈ Work.ThmF.W H t :=
      conj_mem_W_of_mem_centD ((Submission.Blueprint.centD H t).inv_mem hv) hw
    rwa [show v⁻¹ * (v * w * v⁻¹) * (v⁻¹)⁻¹ = w by group] at h1

/-- A subgroup of prime order is commutative. -/
private theorem comm_of_prime_card {G : Type} [Group G] {P : Subgroup G}
    (hP : (Nat.card P).Prime) : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p := by
  haveI : Fact (Nat.card ↥P).Prime := ⟨hP⟩
  haveI : IsCyclic ↥P := isCyclic_of_prime_card (p := Nat.card ↥P) rfl
  haveI : IsMulCommutative ↥P := IsCyclic.isMulCommutative
  intro p hp q hq
  exact congrArg Subtype.val
    (IsMulCommutative.is_comm.comm (⟨p, hp⟩ : ↥P) (⟨q, hq⟩ : ↥P))

theorem commV_mem_W {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) :
    ∀ a ∈ Submission.Blueprint.centD H t, ∀ b ∈ Submission.Blueprint.centD H t,
      a * b * a⁻¹ * b⁻¹ ∈ Work.ThmF.W H t := by
  have hPW : P ≤ Subgroup.normalizer (Work.ThmF.W H t : Set G) :=
    fun _ hp => centD_le_normalizer_W (P_le_centD h15 hp)
  intro a ha b hb
  rw [← h15.hV] at ha hb
  exact commutator_mem_of_le_normalizer hPW (comm_of_prime_card c.P_prime) a ha b hb

end Work.ThmF.ChV3.Prove
