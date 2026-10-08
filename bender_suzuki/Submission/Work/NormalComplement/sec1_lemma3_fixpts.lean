import Mathlib
import Submission.Work.NormalComplement.Design.Extra

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- **Peterfalvi I Ch. III §1 Lemma 3, fixed-point count** (p.175).

Standing situation of §1 Lemma 3: `Q = {1} ∪ Inv(N_H(X))` is a subgroup (so that, all its
non-identity elements being involutions, `Q` is elementary abelian of exponent `2`),
`K₁ = N_K(X)` acts *regularly* on `Q#` by conjugation (`hreg`), the `V`-part normalises `K₁`
(`hU`), `P ≤ V ∩ N(X)` centralises `u ∈ Q#` and acts *fixed-point-freely* on `K₁` (`hfpf`).

The content is the orbit-counting step quoted in the design
(`Submission/Work/NormalComplement/_design/Sec3.lean`, proof of `sec1_lemma3`): every
`1 ≠ P₁ ≤ P` fixes exactly one nontrivial point of `Q`, namely `u` (`|C_Q(P₁)| = 2`).

Proof.  `1` and `u` are fixed by `P₁` (as `P₁ ≤ P ≤ C_G({u})`), so `2 ≤ |C_Q(P₁)|`.  Conversely
let `x ∈ Q#` be fixed by `P₁`.  By regularity of `K₁` there is a unique `k ∈ K₁` with
`k u k⁻¹ = x`.  For `1 ≠ p ∈ P₁`: since `P₁ ≤ P ≤ V ∩ N(X) ≤ N(K₁)` we have `p k p⁻¹ ∈ K₁`, and
since `p` commutes with both `u` and `x` we get `(p k p⁻¹) u (p k p⁻¹)⁻¹ = x`; uniqueness forces
`p k p⁻¹ = k`, and fixed-point-freeness of `P` on `K₁` gives `k = 1`, whence `x = u`.  So
`C_Q(P₁) = {1, u}` and `|C_Q(P₁)| = 2`. -/
theorem sec1_lemma3_fixpts {G : Type} [Group G] [Finite G]
    {H X P Q K₁ : Subgroup G} {t u : G}
    (hK : (K₁ : Set G) = Work.NormalComplement.Design.NK H t X)
    (hQ : (Q : Set G) = insert 1 (Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G)))
    (hreg : ∀ a ∈ Q, a ≠ 1 → ∀ b ∈ Q, b ≠ 1 →
      ∃! k : G, k ∈ K₁ ∧ k * a * k⁻¹ = b)
    (hU : Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ≤
        Subgroup.normalizer (K₁ : Set G))
    (huQ : u ∈ Q) (hu1 : u ≠ 1)
    (hP : P ≤ Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G))
    (hPu : P ≤ Subgroup.centralizer ({u} : Set G))
    (hfpf : Work.NormalComplement.Design.FpfOn P
        (Work.NormalComplement.Design.NK H t X)) :
    ∀ P₁ : Subgroup G, P₁ ≤ P → P₁ ≠ ⊥ →
      Nat.card ↥(Q ⊓ Subgroup.centralizer (P₁ : Set G)) = 2 := by
  intro P₁ hP₁P hP₁ne
  -- `u` is fixed by `P₁`, because `P₁ ≤ P ≤ C_G({u})`.
  have huCen : u ∈ Subgroup.centralizer (P₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (hPu (hP₁P hh)) u (by simp)).symm
  -- The fixed points of `P₁` on `Q` are exactly `{1, u}`.
  have hmem : ∀ x : G, x ∈ (Q ⊓ Subgroup.centralizer (P₁ : Set G)) ↔ x = 1 ∨ x = u := by
    intro x
    rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxQ, hxCen⟩
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · right
        -- a nontrivial element `p` of `P₁`
        obtain ⟨p, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP₁ne
        have hpG_ne : (p : G) ≠ 1 := fun hh => hp1 (Subtype.ext hh)
        have hpP₁ : (p : G) ∈ P₁ := p.2
        have hpP : (p : G) ∈ P := hP₁P hpP₁
        -- regularity of `K₁` on `Q#`: a unique `k` with `k u k⁻¹ = x`
        obtain ⟨k, ⟨hkK₁, hku⟩, huniq⟩ := hreg u huQ hu1 x hxQ hx1
        -- `p` commutes with `u` and with `x`
        have hpu : (p : G) * u = u * (p : G) :=
          ((Subgroup.mem_centralizer_iff.mp (hPu hpP)) u (by simp)).symm
        have hpx : (p : G) * x = x * (p : G) :=
          (Subgroup.mem_centralizer_iff.mp hxCen) (p : G) hpP₁
        -- `P₁ ≤ V ∩ N(X) ≤ N(K₁)`, so `p` conjugates `K₁` to itself
        have hpk : (p : G) * k * (p : G)⁻¹ ∈ K₁ :=
          (Subgroup.mem_normalizer_iff.mp (hU (hP hpP)) k).mp hkK₁
        -- conjugating `u` by `p k p⁻¹` again gives `x`
        have hconj : ((p : G) * k * (p : G)⁻¹) * u * ((p : G) * k * (p : G)⁻¹)⁻¹ = x := by
          have hpu' : (p : G) * u * (p : G)⁻¹ = u := by
            rw [hpu, mul_assoc, mul_inv_cancel, mul_one]
          have hpx' : (p : G) * x * (p : G)⁻¹ = x := by
            rw [hpx, mul_assoc, mul_inv_cancel, mul_one]
          have hpu'' : (p : G)⁻¹ * u * (p : G) = u := by
            calc (p : G)⁻¹ * u * (p : G) = (p : G)⁻¹ * (u * (p : G)) := by rw [mul_assoc]
              _ = (p : G)⁻¹ * ((p : G) * u) := by rw [← hpu]
              _ = ((p : G)⁻¹ * (p : G)) * u := by rw [mul_assoc]
              _ = u := by rw [inv_mul_cancel, one_mul]
          calc ((p : G) * k * (p : G)⁻¹) * u * ((p : G) * k * (p : G)⁻¹)⁻¹
              = (p : G) * k * ((p : G)⁻¹ * u * (p : G)) * k⁻¹ * (p : G)⁻¹ := by group
            _ = (p : G) * k * u * k⁻¹ * (p : G)⁻¹ := by rw [hpu'']
            _ = (p : G) * (k * u * k⁻¹) * (p : G)⁻¹ := by group
            _ = (p : G) * x * (p : G)⁻¹ := by rw [hku]
            _ = x := hpx'
        -- uniqueness of `k` forces `p k p⁻¹ = k`, and `P` is fixed-point-free on `K₁`
        have hkeq : (p : G) * k * (p : G)⁻¹ = k := huniq _ ⟨hpk, hconj⟩
        have hk1 : k = 1 := hfpf (p : G) hpP hpG_ne k (hK ▸ hkK₁) hkeq
        rw [hk1] at hku
        simpa using hku.symm
    · rintro (rfl | rfl)
      · exact ⟨Q.one_mem, (Subgroup.centralizer (P₁ : Set G)).one_mem⟩
      · exact ⟨huQ, huCen⟩
  have hset : ((Q ⊓ Subgroup.centralizer (P₁ : Set G)) : Set G) = {1, u} := by
    ext x
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hmem x
  change Nat.card (Q ⊓ Subgroup.centralizer (P₁ : Set G) : Set G) = 2
  rw [Nat.card_coe_set_eq, hset]
  exact Set.ncard_pair hu1.symm

end Work.NormalComplement
