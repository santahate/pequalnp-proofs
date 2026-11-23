import Mathlib.Combinatorics.Hall.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside

open Finset Function

theorem L_lib_127 : ∀ (n : ℕ) (π : Equiv.Perm (Fin n × Bool)), ∃ b : Fin n → Bool, ∃ π₀ π₁ : Equiv.Perm (Fin n), ∀ (ρ : Fin n) (β : Bool), (π (ρ, β)).1 = (if (β != b ρ) = true then π₁ else π₀) ρ := by
  intro n π
  let N (a : Fin n) : Finset (Fin n) := {(π (a, false)).1, (π (a, true)).1}
  have hN (a y : Fin n) : y ∈ N a ↔ ∃ t : Bool, (π (a, t)).1 = y := by
    simp [N, Bool.exists_bool, eq_comm]
  have hall (S : Finset (Fin n)) : S.card ≤ (S.biUnion N).card := by
    have h : (S ×ˢ (univ : Finset Bool)).card ≤ ((S.biUnion N) ×ˢ (univ : Finset Bool)).card := by
      apply Finset.card_le_card_of_injOn π
      · intro p hp
        have ha := (Finset.mem_product.1 hp).1
        exact Finset.mem_product.2 ⟨Finset.mem_biUnion.2 ⟨p.1, ha,
          (hN _ _).2 ⟨p.2, rfl⟩⟩, Finset.mem_univ _⟩
      · intro a _ b _ hab
        exact π.injective hab
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool] at h
    omega
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N).1 hall
  have hchosen : ∀ a, ∃ t : Bool, (π (a, t)).1 = f a := fun a => (hN a (f a)).1 (hmem a)
  choose b hb using hchosen
  let g (a : Fin n) := (π (a, !b a)).1
  have hfb : Bijective f := Finite.injective_iff_bijective.mp hf
  have hgs : Surjective g := by
    intro y
    obtain ⟨a, ha⟩ := hfb.2 y
    let p := π.symm (y, !(π (a, b a)).2)
    have hp : π p = (y, !(π (a, b a)).2) := π.apply_symm_apply _
    have hneq : p.2 ≠ b p.1 := by
      intro hEq
      have he : (p.1, b p.1) = p := Prod.ext rfl hEq.symm
      have haf : f p.1 = f a := by rw [← hb p.1, he, hp, ha]
      have hpa : p = (a, b a) := by rw [← he, hf haf]
      have hbad := congrArg Prod.snd (hpa ▸ hp)
      simp at hbad
    have hbit : p.2 = !b p.1 := by
      cases h₁ : p.2 <;> cases h₂ : b p.1 <;> simp_all
    refine ⟨p.1, ?_⟩
    change (π (p.1, !b p.1)).1 = y
    rw [← hbit, Prod.mk.eta]
    exact congrArg Prod.fst hp
  let π₀ := Equiv.ofBijective f hfb
  let π₁ := Equiv.ofBijective g (Finite.surjective_iff_bijective.mp hgs)
  refine ⟨b, π₀, π₁, ?_⟩
  intro a t
  have hba := hb a
  cases t <;> cases hb' : b a <;> simp [π₀, π₁, g, hb'] at hba ⊢ <;> exact hba

end PEqualNP.Outside
