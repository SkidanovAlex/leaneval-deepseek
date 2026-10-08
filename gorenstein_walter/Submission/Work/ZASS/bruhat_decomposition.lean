import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.card_G
import Submission.Work.ZASS.card_borel
import Submission.Work.ZASS.Basic
import Submission.Work.Zassenhaus.Basic
import Submission.Work.ZASS.conj_unipotent_le_stabilizer_zero
import Submission.Work.ZASS.mem_or_exists_mul_of_card

namespace Work.ZASS

section OrderOfConj

variable {G : Type*} [Group G]

/-- Conjugation preserves the order of an element.  (Not available in Mathlib in this form;
the conjugation map `y ↦ s * y * s⁻¹` is an injective monoid homomorphism.) -/
theorem orderOf_conj (s x : G) : orderOf (s * x * s⁻¹) = orderOf x := by
  have hinj : Function.Injective (fun y : G => s * y * s⁻¹) := by
    intro a b hab
    simpa using (mul_left_cancel (mul_right_cancel hab))
  simpa using
    orderOf_injective
      { toFun := fun y => s * y * s⁻¹
        map_one' := by simp
        map_mul' := by intro a b; simp [mul_assoc] } hinj x

end OrderOfConj

/-- **Z6.1** (HB III XI 1.7a; blueprint design pass 2 §13).  With `s` an involution
interchanging `∞` and `0` and `U` the normal Sylow `p`-subgroup of `B = G_∞`, the map
`B × U → G`, `(b,u) ↦ b s u` is injective (so HB's `G = B ⊔ B s F` has *unique* expression)
and its image together with `B` covers `G`.  Route: `s ∉ B`; `s U s⁻¹ ≤ B₀ = G_0`;
`B ⊓ B₀ = H` meets `s U s⁻¹` trivially because `|sUs⁻¹| = p^k` and `|H| = (p^k-1)/2` are
coprime; the non-`B` elements `B s U` then number `|B|·|U| = qh·q = q²h = |G| - |B|`. -/
theorem bruhat_decomposition {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {p k : ℕ} [Fact p.Prime] (hp : Odd p) (h : Work.GW2.ZassHyps2 G X (p ^ k))
    {inf zero : X} (hne : inf ≠ zero)
    {U : Subgroup G} (hUB : U ≤ Work.Zassenhaus.borel G inf) (hcardU : Nat.card U = p ^ k)
    (hN : (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal)
    {s : G} (hs : s * s = 1) (hsinf : s • inf = zero) (hszero : s • zero = inf) :
    Function.Injective
        (fun q : (Work.Zassenhaus.borel G inf) × U => (q.1 : G) * s * (q.2 : G)) ∧
      ∀ g : G, g ∈ Work.Zassenhaus.borel G inf ∨
        ∃ q : (Work.Zassenhaus.borel G inf) × U, g = (q.1 : G) * s * (q.2 : G) := by
  classical
  -- Normality of `U` in `B` belongs to the intended setting but is not needed for the count.
  have _hN := hN
  set B := Work.Zassenhaus.borel G inf with hBdef
  -- `|B| = q * (q-1)/2` (Z2), `|G| = (q+1) * q * (q-1)/2` (Z1), `|H| = (q-1)/2`, and
  -- `q`, `(q-1)/2` are coprime.
  have hcardB : Nat.card B = p ^ k * ((p ^ k - 1) / 2) := by
    rw [hBdef]; exact card_borel h hne
  have hcardG : Nat.card G = (p ^ k + 1) * p ^ k * ((p ^ k - 1) / 2) := card_G h hne
  have hcardH : Nat.card (Work.Zassenhaus.pairStab G inf zero) = (p ^ k - 1) / 2 :=
    card_pairStab h hne
  have hcop : Nat.Coprime (p ^ k) ((p ^ k - 1) / 2) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · exact Work.Zassenhaus.zass_coprime_pow_half (Fact.out) hp hk
  -- `s ∉ B`, since `s • ∞ = 0 ≠ ∞`.
  have hsB : s ∉ B := by
    intro hsB
    have h1 : s • inf = inf := Work.Zassenhaus.mem_borel_iff.mp (hBdef ▸ hsB)
    rw [hsinf] at h1
    exact hne h1.symm
  -- `s U s⁻¹` fixes `0`.
  have hconj0 : ∀ u ∈ U, s * u * s⁻¹ ∈ MulAction.stabilizer G zero :=
    conj_unipotent_le_stabilizer_zero hUB hs hszero
  -- Injectivity of `(b,u) ↦ b * s * u`: from `b₁ s u₁ = b₂ s u₂` we get
  -- `b₂⁻¹ b₁ = s (u₂ u₁⁻¹) s⁻¹`, an element of `B ⊓ G_0 = H` whose order divides both
  -- `p^k` (it is conjugate to an element of `U`, `|U| = p^k`) and `(p^k-1)/2 = |H|`;
  -- these are coprime, so it is `1`.
  have hinj : Function.Injective (fun q : B × U => (q.1 : G) * s * (q.2 : G)) := by
    rintro ⟨b₁, u₁⟩ ⟨b₂, u₂⟩ heq
    change (b₁ : G) * s * (u₁ : G) = (b₂ : G) * s * (u₂ : G) at heq
    have h1 : ((b₂ : G))⁻¹ * ((b₁ : G)) = s * (((u₂ : G)) * ((u₁ : G))⁻¹) * s⁻¹ := by
      have hmid : ((b₂ : G))⁻¹ * ((b₁ : G)) * s * ((u₁ : G)) = s * ((u₂ : G)) := by
        calc ((b₂ : G))⁻¹ * ((b₁ : G)) * s * ((u₁ : G))
            = ((b₂ : G))⁻¹ * (((b₁ : G)) * s * ((u₁ : G))) := by group
          _ = ((b₂ : G))⁻¹ * (((b₂ : G)) * s * ((u₂ : G))) := by rw [heq]
          _ = s * ((u₂ : G)) := by group
      calc ((b₂ : G))⁻¹ * ((b₁ : G))
          = ((b₂ : G))⁻¹ * ((b₁ : G)) * s * ((u₁ : G)) * ((u₁ : G))⁻¹ * s⁻¹ := by group
        _ = s * ((u₂ : G)) * ((u₁ : G))⁻¹ * s⁻¹ := by rw [hmid]
        _ = s * (((u₂ : G)) * ((u₁ : G))⁻¹) * s⁻¹ := by group
    have hwU : (u₂ : G) * (u₁ : G)⁻¹ ∈ U := U.mul_mem u₂.2 (U.inv_mem u₁.2)
    have htB : ((b₂ : G))⁻¹ * ((b₁ : G)) ∈ B := B.mul_mem (B.inv_mem b₂.2) b₁.2
    have ht0 : ((b₂ : G))⁻¹ * ((b₁ : G)) ∈ MulAction.stabilizer G zero := by
      rw [h1]; exact hconj0 _ hwU
    have htH : ((b₂ : G))⁻¹ * ((b₁ : G)) ∈ Work.Zassenhaus.pairStab G inf zero :=
      Work.Zassenhaus.mem_pairStab_iff.mpr
        ⟨MulAction.mem_stabilizer_iff.mp ht0, Work.Zassenhaus.mem_borel_iff.mp (hBdef ▸ htB)⟩
    have hdvdH : orderOf (((b₂ : G))⁻¹ * ((b₁ : G))) ∣ (p ^ k - 1) / 2 := by
      rw [← hcardH]
      exact Subgroup.orderOf_dvd_natCard _ htH
    have hdvdU : orderOf (((b₂ : G))⁻¹ * ((b₁ : G))) ∣ p ^ k := by
      rw [h1, orderOf_conj]
      rw [← hcardU]
      exact Subgroup.orderOf_dvd_natCard U hwU
    have hone : ((b₂ : G))⁻¹ * ((b₁ : G)) = 1 :=
      orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left hdvdU hcop).eq_one_of_dvd hdvdH)
    have hb1 : b₁ = b₂ := by
      have := congrArg (fun x : G => (b₂ : G) * x) hone
      exact Subtype.ext (by simpa using this)
    have hu1 : u₁ = u₂ := by
      refine Subtype.ext ?_
      have h := heq
      rw [hb1] at h
      exact mul_left_cancel h
    exact Prod.ext hb1 hu1
  refine ⟨hinj, ?_⟩
  -- Covering: `B` and the image of the (injective) map are disjoint (`s ∉ B`) and together
  -- have `|B| * |U| + |B| = |G|` elements, so they fill `G`.
  refine mem_or_exists_mul_of_card B U s hinj ?_ ?_
  · intro b u hmem
    have hsu : s ∈ B := by
      have h1 : (b : G)⁻¹ * ((b : G) * s * (u : G)) * (u : G)⁻¹ = s := by group
      rw [← h1]
      exact B.mul_mem (B.mul_mem (B.inv_mem b.2) hmem) (B.inv_mem (hUB u.2))
    exact hsB hsu
  · rw [hcardG, hcardB, hcardU]; ring

end Work.ZASS
