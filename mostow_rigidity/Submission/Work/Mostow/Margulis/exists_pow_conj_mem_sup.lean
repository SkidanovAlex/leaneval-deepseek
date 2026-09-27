import Mathlib
import Submission.Work.Mostow.Margulis.list_prod_iterate_eq_one
import Submission.Work.Mostow.Margulis.conj_pow_eq_prod

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Mostow.Margulis

/-- **Auxiliary.**  If `K ≤ N` (encoded as `N` being a subgroup of its own right) with `K` normal
in the ambient group `G` and `x ∈ G` normalising `N` and preserving `K`, then conjugation by `x`
descends to an automorphism `e` of `N ⧸ K.subgroupOf N`, and its iterates are induced by
conjugation by the powers `x ^ i`:
`e^[i] (mk n) = mk (x ^ i * n * (x ^ i)⁻¹)`.

(`hxN` and `hxiN` say that conjugation by `x`, respectively by `x⁻¹`, maps `N` into itself; for
the existence of the *inverse* of the descended map the second one is essential.  `hxpow` simply
records the membership of the conjugating elements used in the conclusion.) -/
private theorem quotient_conj_iterate_aux {G : Type*} [Group G] {K N : Subgroup G}
    [hH : (K.subgroupOf N).Normal] {x : G}
    (hK : K.Normal) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hxiN : ∀ n ∈ N, x⁻¹ * n * x ∈ N)
    (hxpow : ∀ (i : ℕ) (n : G), n ∈ N → x ^ i * n * (x ^ i)⁻¹ ∈ N) :
    ∃ e : (N ⧸ K.subgroupOf N) ≃* (N ⧸ K.subgroupOf N),
      ∀ (i : ℕ) (n : N), e^[i] (QuotientGroup.mk' (K.subgroupOf N) n) =
        QuotientGroup.mk' (K.subgroupOf N) ⟨x ^ i * (n : G) * (x ^ i)⁻¹, hxpow i (n : G) n.2⟩ := by
  let e1 : N ≃* N :=
    { toFun := fun n => ⟨x * (n : G) * x⁻¹, hxN n n.2⟩
      invFun := fun n => ⟨x⁻¹ * (n : G) * x, hxiN n n.2⟩
      left_inv := fun n => by ext; group
      right_inv := fun n => by ext; group
      map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
  have hmap : (K.subgroupOf N).map (e1 : N →* N) = K.subgroupOf N := by
    ext n
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      show x * (m : G) * x⁻¹ ∈ K
      exact hK.conj_mem _ hm x
    · intro hn
      refine ⟨e1.symm n, ?_, e1.apply_symm_apply n⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      show x⁻¹ * (n : G) * x ∈ K
      simpa using hK.conj_mem _ hn x⁻¹
  refine ⟨QuotientGroup.congr (K.subgroupOf N) (K.subgroupOf N) e1 hmap, ?_⟩
  have hσgen : ∀ m : N, (QuotientGroup.congr (K.subgroupOf N) (K.subgroupOf N) e1 hmap)
      ((QuotientGroup.mk' (K.subgroupOf N)) m) = (QuotientGroup.mk' (K.subgroupOf N)) (e1 m) :=
    fun m => QuotientGroup.congr_mk _ _ e1 hmap m
  intro i
  induction i with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    rw [Function.iterate_succ_apply', ih n, hσgen]
    congr 1
    apply Subtype.ext
    show x * (x ^ k * (n : G) * (x ^ k)⁻¹) * x⁻¹ = x ^ (k + 1) * (n : G) * (x ^ (k + 1))⁻¹
    rw [pow_succ]
    group

/-- Let `K ≤ N` be normal subgroups of a group `G` with `N/K` finite, and `x ∈ G` such that all
commutators `[g,x] = g x g⁻¹ x⁻¹` lie in `N`.  Then there is a positive `m` with
`g x ^ m g⁻¹ ∈ K ⊔ Subgroup.zpowers (x ^ m)` for every `g`; equivalently `K ⊔ ⟨x^m⟩` is normal in
`G`.

Concretely one may take `m = n! * n` where `n = Nat.card (N ⧸ K.subgroupOf N)`: write
`Q := N ⧸ K.subgroupOf N`, let `σ : Q ≃* Q` be induced by conjugation by `x`; then `σ ^ n! = 1`
(as an `Equiv.Perm` of the `n`-element set `Q`), every element of `Q` has order dividing `n`, and
`g x ^ m g⁻¹ = (∏_{i<m} x^i [g,x] x^{-i}) · x^m` where the parenthesised product is `1` in `Q`
because, splitting the product into `n` blocks of length `n!` (via `Finset.prod_range_add`), it
equals `B ^ n` for a `B ∈ Q`. -/
theorem exists_pow_conj_mem_sup {G : Type*} [Group G] (K N : Subgroup G) (hKN : K ≤ N)
    (hK : K.Normal) (hN : N.Normal) (hfi : (K.subgroupOf N).FiniteIndex) {x : G}
    (hx : ∀ g : G, g * x * g⁻¹ * x⁻¹ ∈ N) :
    ∃ m : ℕ, 0 < m ∧ ∀ g : G, g * x ^ m * g⁻¹ ∈ K ⊔ Subgroup.zpowers (x ^ m) := by
  haveI hH : (K.subgroupOf N).Normal := hK.subgroupOf N
  haveI hfinq : (K.subgroupOf N).FiniteIndex := hfi
  -- ## Step 1: conjugation by `x` and by `x⁻¹` preserves `N`
  have hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro n hn
    have h1 : (n * x * n⁻¹ * x⁻¹)⁻¹ ∈ N := N.inv_mem (hx n)
    have h2 : (n * x * n⁻¹ * x⁻¹)⁻¹ * n ∈ N := N.mul_mem h1 hn
    convert h2 using 1
    group
  have hxiN : ∀ n ∈ N, x⁻¹ * n * x ∈ N := by
    intro n hn
    have h1 : x⁻¹ * n * x * n⁻¹ ∈ N := by
      have h0 := hx (x⁻¹ * n)
      convert h0 using 1
      group
    have h2 : (x⁻¹ * n * x * n⁻¹) * n ∈ N := N.mul_mem h1 hn
    convert h2 using 1
    group
  have hxpow : ∀ (i : ℕ) (n : G), n ∈ N → x ^ i * n * (x ^ i)⁻¹ ∈ N := by
    intro i
    induction i with
    | zero => intro n hn; simpa using hn
    | succ k ih =>
      intro n hn
      have h2 : x * (x ^ k * n * (x ^ k)⁻¹) * x⁻¹ ∈ N := hxN _ (ih n hn)
      convert h2 using 1
      rw [pow_succ]
      group
  -- ## Step 2: the conjugation automorphism of `N/K` induced by `x`
  obtain ⟨e, he⟩ := quotient_conj_iterate_aux (K := K) (N := N) (x := x) hK hxN hxiN hxpow
  -- ## Step 3: `e` has finite order
  haveI : Nonempty (N ⧸ K.subgroupOf N) := ⟨1⟩
  obtain ⟨d, hdpos, hdper⟩ :
      ∃ d : ℕ, 0 < d ∧ ∀ y : N ⧸ K.subgroupOf N, (⇑e : _ → _)^[d] y = y := by
    obtain ⟨d, hdpos, hde⟩ :=
      (isOfFinOrder_of_finite (e.toEquiv : Equiv.Perm (N ⧸ K.subgroupOf N))).exists_pow_eq_one
    refine ⟨d, hdpos, fun y => ?_⟩
    have hfun : (⇑e : N ⧸ K.subgroupOf N → N ⧸ K.subgroupOf N)^[d] = id := by
      show (⇑e.toEquiv : N ⧸ K.subgroupOf N → N ⧸ K.subgroupOf N)^[d] = id
      rw [← Equiv.Perm.coe_pow, hde]
      rfl
    simpa using congrFun hfun y
  -- ## Step 4: the exponent `m = d * Nat.card (N/K)` works
  refine ⟨d * Nat.card (N ⧸ K.subgroupOf N), Nat.mul_pos hdpos Nat.card_pos, ?_⟩
  intro g
  set c : G := g * x * g⁻¹ * x⁻¹ with hcdef
  have hcN : c ∈ N := by rw [hcdef]; exact hx g
  set m : ℕ := d * Nat.card (N ⧸ K.subgroupOf N) with hmdef
  set yl : List N := (List.range m).map (fun i => (⟨x ^ i * c * (x ^ i)⁻¹, hxpow i c hcN⟩ : N))
    with hyldef
  set Pn : N := yl.prod with hPndef
  have hPnG : (Pn : G) = (yl.map (Subgroup.subtype N)).prod :=
    map_list_prod (Subgroup.subtype N) yl
  have hPnG2 : (yl.map (Subgroup.subtype N)).prod
      = ((List.range m).map (fun i => x ^ i * c * (x ^ i)⁻¹)).prod := by
    rw [hyldef, List.map_map]
    congr 1
  have hgoal_eq : g * x ^ m * g⁻¹ = (Pn : G) * x ^ m := by
    have h1 : g * x * g⁻¹ = c * x := by rw [hcdef]; group
    have h2 : g * x ^ m * g⁻¹ = (c * x) ^ m := by
      rw [← h1]
      rw [conj_pow]
    rw [h2, conj_pow_eq_prod x c m, hPnG, hPnG2]
  have hPnK : (Pn : G) ∈ K := by
    have hclass : QuotientGroup.mk' (K.subgroupOf N) Pn = 1 := by
      have hA : QuotientGroup.mk' (K.subgroupOf N) Pn
          = (yl.map (QuotientGroup.mk' (K.subgroupOf N))).prod := by
        rw [hPndef]
        exact map_list_prod (QuotientGroup.mk' (K.subgroupOf N)) yl
      rw [hA, hyldef, List.map_map]
      have hfun : (QuotientGroup.mk' (K.subgroupOf N)) ∘
            (fun i => (⟨x ^ i * c * (x ^ i)⁻¹, hxpow i c hcN⟩ : N))
          = (fun i => (⇑e : N ⧸ K.subgroupOf N → N ⧸ K.subgroupOf N)^[i]
              (QuotientGroup.mk' (K.subgroupOf N) (⟨c, hcN⟩ : N))) := by
        funext i
        exact (he i ⟨c, hcN⟩).symm
      rw [hfun]
      exact list_prod_iterate_eq_one (⇑e) hdpos hdper _
    have hmem := (QuotientGroup.eq_one_iff (N := K.subgroupOf N) Pn).mp hclass
    exact hmem
  rw [hgoal_eq]
  exact mul_mem (Subgroup.mem_sup_left hPnK)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers (x ^ m)))

end Work.Mostow.Margulis
